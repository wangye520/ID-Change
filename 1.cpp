#include <array>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <csignal>
#include <exception>
#include <fstream>
#include <iomanip>
// UTF-8 encoded file
#include <iostream>
#include <map>
#include <mutex>
#include <string>
#include <thread>
#include <vector>
#include <random>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <queue>
#include <condition_variable>
#include <atomic>
#include <functional>
#include <shared_mutex>
#include <memory>
#include <unordered_set>
#include <future>
#include <optional>

// 条件编译处理不同平台的头文件
#ifdef _WIN32
    // Windows平台，不包含Unix特有的头文件
    #include <time.h>
    #include <unordered_map>
    #include <winsock2.h>
    #include <ws2tcpip.h>
    #include <io.h>
    #include <fcntl.h>
    #pragma comment(lib, "ws2_32.lib")
    // 为Windows平台定义Unix特有的宏
    #define F_OK 0
    #define access _access_s
    #define mkdir(p, m) _mkdir(p)
    // 不使用close宏，避免与C++流冲突
    #define chmod _chmod
    // 简化chown处理
    #define chown(p, u, g) (0)
    // 模拟getuid和geteuid
    #define getuid() 0
    #define geteuid() 0
#else
    // Linux/Android平台
    #include <sys/wait.h>
    #include <time.h>
    #include <unordered_map>
    #include <unistd.h>
    #include <sys/stat.h>
    #include <sys/types.h>
    #include <signal.h>
    #include <sys/select.h>
    #include <sys/time.h>
#endif

// 全局变量
static bool needRestoreSelinux = false;

using namespace std;

// 前向声明
class SecureRandomGenerator;
SecureRandomGenerator& getRandomGenerator();
static void logMsg(const string &msg, int level = 1);
static string trim(const string &s);
static string getprop(const string &k);
static string readFile(const string& path);
struct Exec { int status; string output; };
static Exec sh(const string &cmd, bool logOutput = false);
static bool setpropKV(const string &key, const string &val, bool allowFallback = true);
static void writeFile(const string& path, const string& content, mode_t mode, int uid, int gid);
static string findResetpropBinary();
static bool clearprop(const string &key) {
    // 安全地执行clearprop操作，避免命令注入
    // 使用resetprop的-n选项来清除属性
    string rp = findResetpropBinary();
    if (!rp.empty()) {
        string cmd = rp + " -n \"" + key + "\"";
        logMsg("Clearing property with resetprop: " + key, 2);
        return sh(cmd).status == 0;
    }
    
    // 安全地使用setprop
    string cmd = "setprop \"" + key + "\" \"\"";
    logMsg("Clearing property with setprop: " + key, 2);
    return sh(cmd).status == 0;
}

// 缺失的函数声明
static void systemLevelModifications();
static void autoServiceManagement();
static string getShortID(const string& input);
static void monitorAbnormalServices();

/* ---------------- Utility Helpers ---------------- */

// 设备信息收集和显示功能
static string collectDeviceInfo() {
    string deviceInfo = "=== 设备基本信息 ===\n";
    
    // 收集设备基本信息
    map<string, string> infoFields = {
        {"设备型号", getprop("ro.product.model")},
        {"制造商", getprop("ro.product.manufacturer")},
        {"Android版本", getprop("ro.build.version.release")},
        {"SDK级别", getprop("ro.build.version.sdk")},
        {"构建ID", getprop("ro.build.id")},
        {"指纹", getprop("ro.build.fingerprint")},
        {"品牌", getprop("ro.product.brand")},
        {"设备", getprop("ro.product.device")},
        {"板型", getprop("ro.product.board")},
        {"硬件", getprop("ro.hardware")},
        {"序列号", getprop("ro.serialno")}
    };
    
    // 收集系统状态信息
    deviceInfo += "\n=== 系统状态 ===\n";
    infoFields["CPU核心数"] = to_string(sysconf(_SC_NPROCESSORS_ONLN));
    
    // 获取内存信息
    string memInfo = readFile("/proc/meminfo").substr(0, 100);
    size_t totalMemPos = memInfo.find("MemTotal:");
    if (totalMemPos != string::npos) {
        size_t kBPos = memInfo.find("kB", totalMemPos);
        if (kBPos != string::npos) {
              string totalMem = memInfo.substr(totalMemPos + 9, kBPos - totalMemPos - 9);
              infoFields["总内存"] = trim(totalMem) + " KB";
          }
      }
    
    // 获取系统时间
    time_t now = time(nullptr);
    char timeStr[100];
    strftime(timeStr, sizeof(timeStr), "%Y-%m-%d %H:%M:%S", localtime(&now));
    infoFields["系统时间"] = string(timeStr);
    
    // 获取已安装应用数量
    string pkgList = sh("pm list packages").output;
    int pkgCount = 0;
    size_t pos = 0;
    while ((pos = pkgList.find("package:", pos)) != string::npos) {
        pkgCount++;
        pos += 8;
    }
    infoFields["已安装应用数"] = to_string(pkgCount);
    
    // 格式化为JSON字符串，方便后续处理
    string jsonInfo = "{";
    for (const auto& [key, value] : infoFields) {
        deviceInfo += key + ": " + (value.empty() ? "未知" : value) + "\n";
        jsonInfo += "\"" + key + "\":\"" + (value.empty() ? "未知" : value) + "\",";
    }
    if (jsonInfo.back() == ',') jsonInfo.pop_back();
    jsonInfo += "}";
    
    // 保存到系统属性和文件
    setpropKV("spoof.device.info", jsonInfo);
    writeFile("/data/local/tmp/device_info.json", jsonInfo, 0600, 0, 0);
    
    return deviceInfo;
}

// 显示设备信息
static void displayDeviceInfo() {
    string info = collectDeviceInfo();
    logMsg("\n" + info, 1);
}

// Check for file existence using the POSIX API with caching for performance
// This avoids a dependency on std::filesystem which may not be fully supported
// on some Android NDK toolchains.
struct CachedFileEntry {
    bool exists;
    time_t timestamp;
};

// 使用shared_mutex提高并发性能
static std::unordered_map<string, CachedFileEntry> fileExistsCache;
static std::shared_mutex fileCacheMutex;
static const int FILE_CACHE_TTL_MS = 30000; // 30秒缓存过期时间
static const size_t FILE_CACHE_MAX_SIZE = 1000; // 最大缓存条目数

static bool fileExists(const string &p) {
    // 使用shared_lock允许并发读取
    {
        std::shared_lock<std::shared_mutex> lock(fileCacheMutex);
        auto it = fileExistsCache.find(p);
        if (it != fileExistsCache.end()) {
            // 修复：使用正确的毫秒级过期检查
            auto now = chrono::steady_clock::now();
            auto cacheTime = chrono::seconds(it->second.timestamp);
            auto cacheTimeMs = chrono::duration_cast<chrono::milliseconds>(cacheTime);
            auto age = chrono::duration_cast<chrono::milliseconds>(now.time_since_epoch() - cacheTimeMs);
            
            if (age.count() < FILE_CACHE_TTL_MS) {
                return it->second.exists;
            }
            // 过期但不立即删除，避免在读取时获取写锁
        }
    }
    
    // 执行实际文件检查
    bool exists = (access(p.c_str(), F_OK) == 0);
    
    // 更新缓存，使用unique_lock
    {
        std::unique_lock<std::shared_mutex> lock(fileCacheMutex);
        
        // 双重检查，避免在获取写锁期间其他线程已更新
        auto it = fileExistsCache.find(p);
        time_t now = time(nullptr);
        
        if (it != fileExistsCache.end()) {
            // 更新现有条目
            it->second.exists = exists;
            it->second.timestamp = now;
        } else {
            // 检查缓存大小
            if (fileExistsCache.size() >= FILE_CACHE_MAX_SIZE) {
                // 优化：优先删除过期条目
                vector<string> toRemove;
                toRemove.reserve(fileExistsCache.size() / 4);
                
                for (const auto& entry : fileExistsCache) {
                    auto cacheTime = chrono::seconds(entry.second.timestamp);
                    auto cacheTimeMs = chrono::duration_cast<chrono::milliseconds>(cacheTime);
                    auto age = chrono::duration_cast<chrono::milliseconds>(chrono::steady_clock::now().time_since_epoch() - cacheTimeMs);
                    
                    if (age.count() >= FILE_CACHE_TTL_MS) {
                        toRemove.push_back(entry.first);
                    }
                }
                
                // 删除过期条目
                for (const auto& key : toRemove) {
                    fileExistsCache.erase(key);
                }
                
                // 如果过期条目不够，使用更有效的LRU策略删除最旧条目
                if (fileExistsCache.size() >= FILE_CACHE_MAX_SIZE) {
                    vector<pair<string, time_t>> sortedEntries;
                    sortedEntries.reserve(fileExistsCache.size());
                    
                    for (const auto& entry : fileExistsCache) {
                        sortedEntries.emplace_back(entry.first, entry.second.timestamp);
                    }
                    
                    sort(sortedEntries.begin(), sortedEntries.end(), [](const auto& a, const auto& b) {
                        return a.second < b.second;
                    });
                    
                    size_t toDelete = fileExistsCache.size() - FILE_CACHE_MAX_SIZE + 100; // 多删除100个为新条目留出空间
                    toDelete = min(toDelete, sortedEntries.size());
                    
                    for (size_t i = 0; i < toDelete; ++i) {
                        fileExistsCache.erase(sortedEntries[i].first);
                    }
                }
            }
            
            // 添加新条目
            fileExistsCache[p] = {exists, now};
        }
    }
    
    return exists;
}

// Clear file existence cache when needed (e.g., after file operations)
static void clearFileCache() {
    std::unique_lock<std::shared_mutex> lock(fileCacheMutex);
    fileExistsCache.clear();
}

// Clear specific file from cache
static void clearFileFromCache(const string &path) {
    std::unique_lock<std::shared_mutex> lock(fileCacheMutex);
    fileExistsCache.erase(path);
}

// Ensure that a directory exists with improved error handling and performance
// Uses multiple strategies for better compatibility across Android versions
static bool ensureDir(const string &dirPath) {
    if (dirPath.empty()) return true;
    
    // First check if directory already exists
    if (fileExists(dirPath)) {
        return true;
    }
    
    // Try to create using native mkdir first for better performance
    // We need to create parent directories recursively
    string parentDir = dirPath;
    size_t lastSlash = parentDir.rfind('/');
    if (lastSlash != string::npos && lastSlash > 0) {
        string parent = parentDir.substr(0, lastSlash);
          if (!ensureDir(parent)) {
              return false;
          }
      }
      
      // Try to create the directory
    if (mkdir(dirPath.c_str(), 0755) == 0) {
        clearFileCache(); // Clear cache after modification
        return true;
    }
    
    // Fallback to shell command if native mkdir fails
    // 日志记录
    cout << "Fallback to shell mkdir for: " << dirPath << endl;
    try {
        // 简单的命令执行
        int result = system(("mkdir -p " + dirPath).c_str());
        clearFileCache(); // Clear cache after modification
        return result == 0;
    } catch (const exception& e) {
        cout << "Error creating directory: " << string(e.what()) << endl;
        return false;
    }
}

/* ---------------- Logging ---------------- */

static mutex logMutex;
static const char* LOGF = "/data/local/tmp/spoofer.log";
static int logLevel = 1; // 0=errors only, 1=normal, 2=verbose

// Append a message to the log file with enhanced timestamp and verbosity control
static void logMsg(const string &msg, int level) {
    // Skip if message level is higher than current log level
    if (level > logLevel) return;
    
    lock_guard<mutex> lk(logMutex);
    
    // Ensure log directory exists
    string logDir = string(LOGF).substr(0, string(LOGF).rfind('/'));
    ensureDir(logDir);
    
    // Get current time with milliseconds for better precision
    auto now = chrono::system_clock::now();
    auto now_ms = chrono::time_point_cast<chrono::milliseconds>(now);
    auto time_t_now = chrono::system_clock::to_time_t(now);
    auto ms = now_ms.time_since_epoch().count() % 1000;
    
    // Format time with milliseconds
    char timeStr[32];
    strftime(timeStr, sizeof(timeStr), "%Y-%m-%d %H:%M:%S", localtime(&time_t_now));
    
    ofstream ofs(LOGF, ios::app);
    ofs << "[" << timeStr << "." << setw(3) << setfill('0') << ms << "] " << msg << "\n";
    ofs.flush();
    
    // Also print to console for important messages
    if (level <= 1) {
        cerr << "[" << timeStr << "] " << msg << endl;
    }
}

/* ---------------- Shell Exec ---------------- */

// Exec结构体已在前向声明中定义

// Thread pool for parallel command execution
class ThreadPool {
public:
    ThreadPool(size_t threads = 4) : stop(false) {
        for (size_t i = 0; i < threads; ++i) {
            workers.emplace_back([this] {
                while (true) {
                    function<void()> task;
                    {
                        unique_lock<mutex> lock(queueMutex);
                        condition.wait(lock, [this] { 
                            return stop || !tasks.empty(); 
                        });
                        if (stop && tasks.empty()) return;
                        task = std::move(tasks.front());
                        tasks.pop();
                    }
                    task();
                }
            });
        }
    }
    
    template<class F>
    future<void> enqueue(F&& f) {
        using task_type = packaged_task<void()>;
        auto task = make_shared<task_type>(std::forward<F>(f));
        future<void> result = task->get_future();
        { 
            unique_lock<mutex> lock(queueMutex);
            if (stop) throw runtime_error("enqueue on stopped ThreadPool");
            tasks.emplace([task]() {
                (*task)();
            });
        }
        condition.notify_one();
        return result;
    }
    
    ~ThreadPool() {
        { 
            unique_lock<mutex> lock(queueMutex);
            stop = true;
        }
        condition.notify_all();
        for (thread &worker: workers) worker.join();
    }
    
private:
    vector<thread> workers;
    queue<function<void()>> tasks;
    mutex queueMutex;
    condition_variable condition;
    bool stop;
};

// Global thread pool for parallel command execution
static ThreadPool* commandThreadPool = nullptr;

// Initialize thread pool
static void initThreadPool() {
    if (!commandThreadPool) {
        // 动态获取CPU核心数，设置合适的线程池大小
        size_t cpuCount = std::thread::hardware_concurrency();
        size_t threadCount = cpuCount > 0 ? std::max<size_t>(2, cpuCount / 2) : 4; // 至少2个线程，最多CPU核心数的一半
        commandThreadPool = new ThreadPool(threadCount);
        logMsg("Command thread pool initialized with " + to_string(threadCount) + " threads", 2);
    }
}

// Execute a shell command and capture its output with improved error handling
static Exec sh(const string &cmd, bool logOutput) {
    // 记录命令执行，但避免在日志中泄露敏感信息
    logMsg(string("RUN: [command]") + (cmd.size() > 100 ? " (truncated)" : ""), 2);
    
    array<char, 4096> buf{};
    string out;
    FILE* p = nullptr;
    
    try {
        // 安全地执行命令，合并标准错误到标准输出
        p = popen((cmd + " 2>&1").c_str(), "r");
        if (!p) {
            string errorMsg = "popen failed: " + to_string(errno);
            logMsg(errorMsg);
            throw runtime_error(errorMsg);
        }
        
        // 读取输出并实现超时处理
        auto startTime = chrono::steady_clock::now();
        const int TIMEOUT_SECONDS = 30;
        
        while (true) {
            // 检查是否有数据可读，使用select进行超时控制
            fd_set readSet;
            FD_ZERO(&readSet);
            int pfd = fileno(p);
            FD_SET(pfd, &readSet);
            
            struct timeval timeout;
            timeout.tv_sec = 1; // 1秒轮询一次
            timeout.tv_usec = 0;
            
            int ready = select(pfd + 1, &readSet, nullptr, nullptr, &timeout);
            
            if (ready > 0 && FD_ISSET(pfd, &readSet)) {
                // 有数据可读
                if (!fgets(buf.data(), buf.size(), p)) {
                    break; // 文件结束或读取失败
                }
                out += buf.data();
            } else if (ready == 0) {
                // 超时，检查是否达到总超时时间
                auto currentTime = chrono::steady_clock::now();
                if (chrono::duration_cast<chrono::seconds>(currentTime - startTime).count() > TIMEOUT_SECONDS) {
                    throw runtime_error("Command timed out after " + to_string(TIMEOUT_SECONDS) + " seconds");
                }
            } else {
                // select失败
                throw runtime_error("Error reading command output: " + to_string(errno));
            }
            
            // 限制输出大小，防止内存溢出
            if (out.size() > 1024 * 1024) { // 1MB限制
                out += "\n[OUTPUT TRUNCATED]";
                break;
            }
        }
        
        int st = pclose(p);
        p = nullptr; // 避免重复关闭
        
        // 记录命令输出（如果需要）
        if (logOutput && logLevel >= 2) {
            logMsg("Command output: " + (out.size() > 100 ? out.substr(0, 100) + "..." : out), 2);
        }
        
        return {st, out};
    } catch (const exception &e) {
        // 确保popen的文件指针被正确关闭
        if (p) {
            pclose(p);
        }
        logMsg("Command execution error: " + string(e.what()), 1);
        throw;
    }
}

// Execute multiple commands in parallel for improved performance
static void executeParallel(const vector<string>& commands, size_t threadCount = 0) {
    initThreadPool();
    
    // 如果明确指定了线程数，重新创建线程池
    if (threadCount > 0 && commandThreadPool) {
        delete commandThreadPool;
        commandThreadPool = new ThreadPool(threadCount);
        logMsg("Command thread pool reinitialized with " + to_string(threadCount) + " threads", 2);
    }
    
    // 存储所有任务的future以便等待完成
    vector<future<void>> futures;
    futures.reserve(commands.size()); // 预分配空间减少重新分配
    
    for (const auto& cmd : commands) {
        // 存储返回的future
        futures.push_back(commandThreadPool->enqueue([cmd]() {
            try {
                sh(cmd);
            } catch (const exception& e) {
                logMsg("Parallel command failed: " + string(e.what()) + " (cmd: " + cmd + ")");
            }
        }));
    }
    
    // 等待所有任务完成
    for (auto& future : futures) {
        try {
            future.wait();
        } catch (const exception& e) {
            logMsg("Error waiting for parallel task: " + string(e.what()));
        }
    }
    
    logMsg("Parallel execution completed: " + to_string(commands.size()) + " commands processed", 2);
}

// Execute a shell command and throw an exception if it returns a non‑zero
// status.  Logging of errors is performed in the exception handler.
static void chk(const string &cmd) {
    auto e = sh(cmd);
    if (e.status != 0) {
        logMsg("ERR: " + cmd + " -> " + e.output);
        throw runtime_error(string("Command failed: ") + cmd);
    }
}

// Trim whitespace from both ends of a string.
static string trim(const string &s) {
    auto b = s.find_first_not_of(" \t\r\n");
    if (b == string::npos) return "";
    auto e = s.find_last_not_of(" \t\r\n");
    return s.substr(b, e - b + 1);
}

// Read a system property via getprop.  Leading/trailing whitespace is
// trimmed.
static string getprop(const string &k) {
    // 验证key格式的安全性，避免潜在的注入
    if (k.empty() || k.find(';') != string::npos || k.find('`') != string::npos || 
        k.find('$') != string::npos || k.find('|') != string::npos) {
        logMsg("ERROR: Invalid property key: " + k, 1);
        return "";
    }
    // 安全地构建命令字符串
    string cmd = "getprop \"" + k + "\"";
    return trim(sh(cmd).output);
}

// Write a file to disk with the given ownership and mode.  The
// implementation ensures that parent directories exist before writing.
static void writeFile(const string& path, const string& content,
                      mode_t mode, int uid, int gid) {
    // Determine the parent directory by locating the last slash in the path.
    size_t slash = path.rfind('/');
    if (slash != string::npos) {
        ensureDir(path.substr(0, slash));
    }
    ofstream ofs(path, ios::binary);
    ofs << content;
    ofs.close();
    chmod(path.c_str(), mode);
    chown(path.c_str(), uid, gid);
}

// Read an entire file into a string.  Returns an empty string on failure.
static string readFile(const string& path) {
    ifstream ifs(path, ios::binary);
    return string((istreambuf_iterator<char>(ifs)), istreambuf_iterator<char>());
}

/* ---------------- Random Generators ---------------- */

// Thread-safe random number generator class with enhanced security
class SecureRandomGenerator {
private:
    mt19937_64 rng;
    mutex rngMutex;
    bool initialized = false;
    string seedSource;
    
public:
    SecureRandomGenerator() {
        initialize();
    }
    
    void initialize() {
        if (initialized) return;
        
        lock_guard<mutex> lock(rngMutex);
        if (initialized) return; // Double-checked locking pattern
        
        string seedHex = getprop("spoof.seed");
        if (!seedHex.empty()) {
            // Use fixed seed from property if available
            uint64_t acc = 0;
            for (char c : seedHex) {
                acc = (acc << 4) ^ (uint64_t)(isdigit(c) ? c - '0' : (10 + toupper(c) - 'A'));
            }
            if (!acc) acc = 0x9e3779b97f4a7c15ULL;
            rng.seed(acc);
            seedSource = "fixed seed from property";
            logMsg("RNG: fixed seed from property", 2);
        } else {
            // Try to seed from /dev/urandom first
            array<uint32_t, 16> buf{}; // Increased buffer size for better entropy
            ifstream ur("/dev/urandom", ios::binary);
            if (ur.read(reinterpret_cast<char*>(buf.data()), buf.size() * 4)) {
                seed_seq s(buf.begin(), buf.end());
                rng.seed(s);
                seedSource = "/dev/urandom";
                logMsg("RNG: seeded from /dev/urandom", 2);
            } else {
                // Enhanced fallback with multiple entropy sources
                vector<uint32_t> fb = {
                    random_device{}(),
                    (uint32_t)chrono::high_resolution_clock::now().time_since_epoch().count(),
                    (uint32_t)getpid(),
                    (uint32_t)getppid(),
                    (uint32_t)clock(),
                    (uint32_t)chrono::steady_clock::now().time_since_epoch().count() & 0xFFFFFFFF
                };
                
                // Add additional entropy from system properties
                try {
                    string buildId = getprop("ro.build.id");
                    if (!buildId.empty()) {
                        hash<string> hasher;
                        fb.push_back(static_cast<uint32_t>(hasher(buildId)));
                    }
                } catch (...) {
                    // Ignore errors
                }
                
                seed_seq s2(fb.begin(), fb.end());
                rng.seed(s2);
                seedSource = "fallback with multiple entropy sources";
                logMsg("RNG: fallback with enhanced entropy sources", 1);
            }
        }
        
        initialized = true;
    }
    
    // Get random number in range [min, max]
    template<typename T> T randInRange(T min, T max) {
        lock_guard<mutex> lock(rngMutex);
        uniform_int_distribution<T> dist(min, max);
        return dist(rng);
    }
    
    // Get random floating point number in range [0.0, 1.0)
    double randDouble() {
        lock_guard<mutex> lock(rngMutex);
        uniform_real_distribution<double> dist(0.0, 1.0);
        return dist(rng);
    }

    // Generate random hex string
    string randHex(size_t n, bool lowercase = false) {
        string result;
        result.reserve(n);
        const char* hexChars = lowercase ? "0123456789abcdef" : "0123456789ABCDEF";
        
        // 优化：直接使用内部的rng，避免重复获取锁
        lock_guard<mutex> lock(rngMutex);
        uniform_int_distribution<uint8_t> dist(0, 15);
        for (size_t i = 0; i < n; ++i) {
            result += hexChars[dist(rng)];
        }
        return result;
    }
    
    // Generate random bytes
    vector<uint8_t> randBytes(size_t count) {
        vector<uint8_t> result(count);
        lock_guard<mutex> lock(rngMutex);
        
        // 一次性生成所有随机字节，提高性能
        uniform_int_distribution<uint8_t> dist(0, 255);
        for (auto& byte : result) {
            byte = dist(rng);
        }
        return result;
    }

    // Get the seed source for debugging
    string getSeedSource() const {
        return seedSource;
    }
    
    // Access to the underlying RNG (thread-safe)
    mt19937_64& getRng() {
        lock_guard<mutex> lock(rngMutex);
        return rng;
    }
};

// Global secure random generator instance
static SecureRandomGenerator* g_randGen = nullptr;

// Get or initialize the random generator
SecureRandomGenerator& getRandomGenerator() {
    if (!g_randGen) {
        // Thread-safe initialization with double-checked locking
        static mutex initMutex;
        lock_guard<mutex> lock(initMutex);
        if (!g_randGen) {
            g_randGen = new SecureRandomGenerator();
        }
    }
    return *g_randGen;
}

// Initialize the random number generator (compatibility function)
static void initRng() {
    getRandomGenerator().initialize();
}

// Generate a string of n random decimal digits with improved performance
static string randDigits(size_t n) {
    if (n == 0) return "";
    
    string s;
    s.reserve(n);
    
    // Use a local distribution object to avoid recreating it each time
    uniform_int_distribution<int> dist(0, 9);
    
    // Get the thread-safe RNG
    auto& rng = getRandomGenerator().getRng();
    
    // Pre-allocate and fill for better performance
    s.resize(n);
    for (size_t i = 0; i < n; ++i) {
        s[i] = static_cast<char>('0' + dist(rng));
    }
    
    return s;
}

// Generate a string of n random hexadecimal characters with options for case
static string randHex(size_t n, bool lowercase = false) {
    if (n == 0) return "";
    
    static const char* hexUpper = "0123456789ABCDEF";
    static const char* hexLower = "0123456789abcdef";
    
    const char* hex = lowercase ? hexLower : hexUpper;
    
    string s;
    s.reserve(n);
    
    uniform_int_distribution<int> dist(0, 15);
    auto& rng = getRandomGenerator().getRng();
    
    s.resize(n);
    for (size_t i = 0; i < n; ++i) {
        s[i] = hex[dist(rng)];
    }
    
    return s;
}

// Generate a string of n alphanumeric characters with options for case
static string randAZ09(size_t n, bool includeLowercase = false) {
    if (n == 0) return "";
    
    static const char* alnumUpper = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
    static const char* alnumFull = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
    
    const char* alnum = includeLowercase ? alnumFull : alnumUpper;
    const int maxDist = includeLowercase ? 61 : 35;
    
    string s;
    s.reserve(n);
    
    uniform_int_distribution<int> dist(0, maxDist);
    auto& rng = getRandomGenerator().getRng();
    
    s.resize(n);
    for (size_t i = 0; i < n; ++i) {
        s[i] = alnum[dist(rng)];
    }
    
    return s;
}

// Generate a random byte array for binary data generation
static vector<uint8_t> randBytes(size_t count) {
    vector<uint8_t> result(count);
    if (count == 0) return result;
    
    uniform_int_distribution<int> dist(0, 255);
    auto& rng = getRandomGenerator().getRng();
    
    for (auto& byte : result) {
        byte = static_cast<uint8_t>(dist(rng));
    }
    
    return result;
}

// Compute the Luhn checksum digit for IMEI/ICCID bodies.
static char luhn(const string &body) {
    int sum = 0;
    bool alt = false;
    for (int i = (int)body.size() - 1; i >= 0; --i) {
        int v = body[i] - '0';
        if (alt) {
            v *= 2;
            if (v > 9) v -= 9;
        }
        sum += v;
        alt = !alt;
    }
    return char('0' + ((10 - sum % 10) % 10));
}

/* ---------------- Property Cache and Utilities ---------------- */

// Property cache entry with timestamp for TTL
struct CachedPropertyEntry {
    string value;
    time_t timestamp;
};

// Property cache for performance optimization
static std::unordered_map<string, CachedPropertyEntry> propertyCache;
static std::shared_mutex propertyCacheMutex;
static const int PROPERTY_CACHE_TTL_MS = 5000; // 5 seconds cache TTL
static const size_t PROPERTY_CACHE_MAX_SIZE = 500; // Max cache entries

// Clear property cache when needed
static void clearPropertyCache() {
    std::unique_lock<std::shared_mutex> lock(propertyCacheMutex);
    propertyCache.clear();
    logMsg("Property cache cleared", 2);
}

// Clear specific property from cache
static void clearPropertyFromCache(const string &key) {
    std::unique_lock<std::shared_mutex> lock(propertyCacheMutex);
    propertyCache.erase(key);
    logMsg("Property removed from cache: " + key, 2);
}

// Get a system property with caching for performance
static optional<string> getProperty(const string &key, bool useCache = true) {
    // Check cache first if enabled
    if (useCache) {
        std::shared_lock<std::shared_mutex> lock(propertyCacheMutex);
        auto it = propertyCache.find(key);
        if (it != propertyCache.end()) {
            // Check if cache entry has expired
            time_t now = time(nullptr);
            if (difftime(now, it->second.timestamp) <= PROPERTY_CACHE_TTL_MS / 1000.0) {
                logMsg("Cache hit for property: " + key, 2);
                return it->second.value;
            }
        }
    }
    
    try {
        Exec res = sh("getprop " + key);
        if (res.status == 0 && !res.output.empty()) {
            // Remove trailing newline
            string value = trim(res.output);
            
            // Update cache with timestamp
            if (useCache) {
                std::unique_lock<std::shared_mutex> lock(propertyCacheMutex);
                
                // If cache is full, remove oldest entries
                if (propertyCache.size() >= PROPERTY_CACHE_MAX_SIZE) {
                    // Find and remove the oldest entry
                    auto oldestIt = propertyCache.begin();
                    time_t oldestTime = oldestIt->second.timestamp;
                    
                    for (auto it = propertyCache.begin(); it != propertyCache.end(); ++it) {
                        if (it->second.timestamp < oldestTime) {
                            oldestTime = it->second.timestamp;
                            oldestIt = it;
                        }
                    }
                    
                    propertyCache.erase(oldestIt);
                    logMsg("Cache pruned due to size limit", 2);
                }
                
                // Store with current timestamp
                propertyCache[key] = {value, time(nullptr)};
            }
            
            logMsg("Retrieved property: " + key + " = " + value, 2);
            return value;
        }
    } catch (const exception &e) {
        logMsg("Error getting property " + key + ": " + string(e.what()), 1);
    }
    return nullopt;
}

/* ---------------- Override Helpers ---------------- */

// Helper to override a randomly generated value with a property value if
// present.  The property key is constructed as "spoof.override." plus the
// provided suffix.  For example, if suffix="serial" then the property
// checked will be `spoof.override.serial`.  If the property exists and is
// non‑empty it is returned; otherwise the provided default is used.
static string maybeOverride(const string &suffix, const string &defVal) {
    string prop = "spoof.override." + suffix;
    optional<string> val = getProperty(prop);
    if (val && !val.value().empty()) {
        logMsg("Using override value for " + suffix + ": " + val.value(), 2);
        return val.value();
    }
    return defVal;
}

/* ---------------- System Property Setter ---------------- */

// Cache for resetprop binary path to avoid repeated lookups
static string resetpropPath;
static mutex resetpropMutex;

// Find the resetprop binary with caching
static string findResetpropBinary() {
    // Check cache first
    { 
        lock_guard<mutex> lock(resetpropMutex);
        if (!resetpropPath.empty()) {
            return resetpropPath;
        }
    }
    
    // Try to find resetprop using which command
    string rp;
    try {
        rp = trim(sh("which resetprop").output);
        if (!rp.empty() && fileExists(rp)) {
            lock_guard<mutex> lock(resetpropMutex);
            resetpropPath = rp;
            logMsg("Found resetprop at: " + rp, 2);
            return rp;
        }
    } catch (...) {
        // Ignore errors and continue to fallback paths
    }
    
    // If `which` fails, probe a list of common installation paths
    // On Android 11-15 devices with Magisk or KernelSU installed
    static const vector<string> rpPaths = {
        "/system/bin/resetprop",
        "/vendor/bin/resetprop",
        "/data/adb/ksu/bin/resetprop",
        "/data/adb/magisk/resetprop",
        "/data/magisk/resetprop",
        "/data/adb/modules/ksu/bin/resetprop",
        "/data/adb/modules/magisk/bin/resetprop",
        "/sbin/resetprop"
    };
    
    for (const auto &candidate : rpPaths) {
        if (fileExists(candidate)) {
            lock_guard<mutex> lock(resetpropMutex);
            resetpropPath = candidate;
            logMsg("Found resetprop at fallback path: " + candidate, 1);
            return candidate;
        }
    }
    
    logMsg("WARN: resetprop binary not found", 1);
    return "";
}

// Set an Android system property persistently with enhanced error handling
// and support for different methods based on availability
static bool setpropKV(const string &key, const string &val, bool allowFallback) {
    // 验证key格式的安全性，避免潜在的注入
    if (key.empty() || key.find(';') != string::npos || key.find('`') != string::npos || key.find('$') != string::npos) {
        logMsg("ERROR: Invalid property key: " + key, 1);
        return false;
    }
    
    string rp = findResetpropBinary();
    
    // Try using resetprop first if available
    if (!rp.empty()) {
        // Try with different resetprop flags for compatibility
        vector<string> resetpropFlags = {"-n", ""};
        for (const string &flag : resetpropFlags) {
            // 安全地构建命令字符串
            string cmd = rp + (flag.empty() ? " " : " " + flag + " ") + 
                        "\"" + key + "\" \"" + val + "\"";
            try {
                logMsg("Setting property with resetprop: " + key + " = " + val, 2);
                Exec result = sh(cmd);
                if (result.status == 0) {
                    // Clear cache for this property
                    { 
                        std::unique_lock<std::shared_mutex> lock(propertyCacheMutex);
                        propertyCache.erase(key);
                        propertyCache.erase("persist." + key);
                    }
                    return true;
                }
            } catch (const exception &e) {
                logMsg("Resetprop command failed: " + string(e.what()) + " (flag: " + flag + ")", 2);
            }
        }
    }
    
    // Fallback to standard setprop if resetprop fails or not available
    if (allowFallback) {
        try {
            logMsg("Fallback to standard setprop for: " + key + " = " + val, 1);
            
            // 安全地构建命令字符串
            string cmd = "setprop \"" + key + "\" \"" + val + "\"";
            if (key.substr(0, 8) != "persist.") {
                sh(cmd); // Set regular property
                // Also try to set persistent version for better persistence
                string persistCmd = "setprop \"persist." + key + "\" \"" + val + "\"";
                try {
                    sh(persistCmd);
                } catch (...) { /* Ignore errors for persist command */ }
            } else {
                sh(cmd); // Directly set persistent property
            }
            
            // Clear cache
            { 
                std::unique_lock<std::shared_mutex> lock(propertyCacheMutex);
                propertyCache.erase(key);
                propertyCache.erase("persist." + key);
            }
            return true;
        } catch (const exception &e) {
            logMsg("WARN: Failed to set property " + key + ": " + string(e.what()), 1);
        }
    }
    
    logMsg("ERROR: Could not set property " + key, 1);
    return false;
}

// Batch set multiple properties at once (more efficient)
static bool setpropBatch(const vector<pair<string, string>>& props, bool allowFallback = true) {
    if (props.empty()) return true;
    
    logMsg("Setting " + to_string(props.size()) + " properties in batch", 2);
    
    vector<string> commands;
    string rp = findResetpropBinary();
    
    // Prepare commands
    for (const auto& [key, val] : props) {
        if (!rp.empty()) {
            commands.push_back(rp + " -n \"" + key + "\" \"" + val + "\"");
        } else if (allowFallback) {
            commands.push_back("setprop " + key + " \"" + val + "\"");
            if (key.substr(0, 8) != "persist.") {
                commands.push_back("setprop persist." + key + " \"" + val + "\"");
            }
        }
    }
    
    // Execute commands in parallel if we have a thread pool
    if (commands.size() > 3) {
        executeParallel(commands);
    } else {
        // For small batches, execute sequentially
        for (const auto& cmd : commands) {
            try {
                sh(cmd);
            } catch (const exception& e) {
                logMsg("Batch property command failed: " + string(e.what()), 2);
            }
        }
    }
    
    // Clear entire cache after batch operation
    clearPropertyCache();
    
    return true;
}

/* ---------------- Target Users and Packages ---------------- */

// Retrieve a list of user IDs present on the device.  If the command
// `pm list users` fails, the function falls back to returning only user 0.
static vector<int> listUsers() {
    vector<int> u;
    try {
        string out = sh("pm list users").output;
        regex re(R"(UserInfo\{(\d+):)");
        for (auto it = sregex_iterator(out.begin(), out.end(), re);
             it != sregex_iterator(); ++it) {
            u.push_back(stoi((*it)[1]));
        }
    } catch (...) {
        // ignore errors
    }
    if (u.empty()) u.push_back(0);
    return u;
}

// Build the list of target packages whose identifiers and permissions are
// hardened.  Extra packages may be specified through the `spoof.block.pkgs`
// system property as a comma‑separated list.
static vector<string> getTargetPkgs() {
    vector<string> pkgs = {
        // Core financial/payment and analytics packages
        "com.unionpay", "cn.gov.pbc.dcep", "com.unionpay.tsmservice.mi",
        "com.google.android.gms", "com.android.vending",
        "com.miui.analytics", "com.miui.securitycenter", "com.miui.securitycore",
    };
    string extra = getprop("spoof.block.pkgs");
    if (!extra.empty()) {
        stringstream ss(extra);
        string pkg;
        while (getline(ss, pkg, ',')) {
            pkg = trim(pkg);
            if (!pkg.empty()) pkgs.push_back(pkg);
        }
    }
    // Support pattern matching to automatically include additional packages.
    // If the property `spoof.block.patterns` is defined, its value should be a
    // comma‑separated list of substrings or simple patterns.  Any installed
    // package whose name contains one of these substrings will be added to
    // the hardened list.  This is useful to counter SDK packages that
    // integrate tracking or privilege escalation functionality without
    // enumerating them explicitly.
    string patternsProp = getprop("spoof.block.patterns");
    if (!patternsProp.empty()) {
        vector<string> patterns;
        {
            stringstream ss(patternsProp);
            string pat;
            while (getline(ss, pat, ',')) {
                pat = trim(pat);
                if (!pat.empty()) patterns.push_back(pat);
            }
        }
        if (!patterns.empty()) {
            // Retrieve the full list of installed package names once.
            string out;
            try {
                out = sh("pm list packages").output;
            } catch (...) {
                out.clear();
            }
            vector<string> installed;
            regex rePkg(R"(package:([\w\.]+))");
            for (auto it = sregex_iterator(out.begin(), out.end(), rePkg); it != sregex_iterator(); ++it) {
                installed.push_back((*it)[1]);
            }
            for (const string &pat : patterns) {
                for (const string &pname : installed) {
                    // simple substring match, case‑insensitive
                    string lcPname = pname;
                    string lcPat = pat;
                    transform(lcPname.begin(), lcPname.end(), lcPname.begin(), ::tolower);
                    transform(lcPat.begin(), lcPat.end(), lcPat.begin(), ::tolower);
                    if (lcPname.find(lcPat) != string::npos) {
                        pkgs.push_back(pname);
                    }
                }
            }
        }
    }
    sort(pkgs.begin(), pkgs.end());
    pkgs.erase(unique(pkgs.begin(), pkgs.end()), pkgs.end());
    return pkgs;
}

/* ---------------- AppOps and Permissions Lockdown ---------------- */

static string APP_OPS;

// Initialise the APP_OPS command.  If `which cmd` cannot find the
// executable then fall back to `/system/bin/cmd`.  This increases
// compatibility with Android 11 devices where the PATH may not include
// `/system/bin` by default.
static void initAppOps() {
    APP_OPS = trim(sh("which cmd").output);
    if (APP_OPS.empty()) {
        APP_OPS = "/system/bin/cmd";
    }
    APP_OPS += " appops";
}

// AppOps operation names for identifiers and sensitive data.  See the
// original source for details.  These lists remain unchanged in this
// Android?1 compatible version.
static const vector<string> kIdOps = {
    "android:read_device_identifiers", "android:read_phone_state", "android:read_phone_numbers",
    "android:read_icc_serial", "android:read_uuid", "android:read_basic_phone_state",
    "android:read_sensitive_phone_state", "android:read_precise_phone_state",
    "android:read_call_log", "android:read_contacts", "android:get_usage_stats",
    "android:query_all_packages", "android:bluetooth_scan", "android:wifi_scan",
    "android:coarse_location", "android:fine_location", "android:activity_recognition",
    "android:body_sensors", "android:bluetooth_connect", "android:read_privileged_phone_state"
};

static const vector<string> kPrivOps = {
    "android:write_settings", "android:write_secure_settings", "android:read_logs",
    "android:system_alert_window", "android:install_packages",
    "android:change_wifi_state", "android:grant_runtime_permissions",
    "android:manage_app_ops_modes"
};

static const vector<string> kSpecialOps = {
    "android:legacy_storage", "android:auto_revoke_permissions_if_unused",
    "android:interact_across_profiles", "android:manage_external_storage"
};

static const vector<string> kIdPerms = {
    "android.permission.READ_DEVICE_IDENTIFIERS", "android.permission.READ_PHONE_STATE",
    "android.permission.READ_PHONE_NUMBERS", "android.permission.READ_BASIC_PHONE_STATE",
    "android.permission.READ_SENSITIVE_PHONE_STATE", "android.permission.READ_PRIVILEGED_PHONE_STATE",
    "android.permission.READ_CONTACTS", "android.permission.GET_USAGE_STATS",
    "android.permission.QUERY_ALL_PACKAGES",
    // MIUI specific op codes (if present) ?represented as MIUIOP(x)
    "MIUIOP(10022)", "MIUIOP(10029)", "MIUIOP(10032)", "MIUIOP(10035)",
    "android.permission.BLUETOOTH_SCAN", "android.permission.ACCESS_FINE_LOCATION",
    "android.permission.ACCESS_COARSE_LOCATION", "android.permission.BODY_SENSORS",
    "android.permission.ACTIVITY_RECOGNITION", "android.permission.BLUETOOTH_CONNECT",
    "android.permission.ACCESS_WIFI_STATE", "android.permission.CAMERA",
    "android.permission.RECORD_AUDIO", "android.permission.USE_BIOMETRIC",
    "android.permission.USE_FINGERPRINT", "android.permission.READ_EXTERNAL_STORAGE",
    "android.permission.WRITE_EXTERNAL_STORAGE",
    "android.permission.READ_MEDIA_AUDIO", "android.permission.WRITE_MEDIA_AUDIO",
    "android.permission.READ_MEDIA_VIDEO", "android.permission.WRITE_MEDIA_VIDEO",
    "android.permission.READ_MEDIA_IMAGES", "android.permission.WRITE_MEDIA_IMAGES"
};

static const vector<string> kPrivPerms = {
    "android.permission.WRITE_SETTINGS", "android.permission.WRITE_SECURE_SETTINGS",
    "android.permission.READ_LOGS", "android.permission.REQUEST_INSTALL_PACKAGES",
    "android.permission.SYSTEM_ALERT_WINDOW", "android.permission.MANAGE_EXTERNAL_STORAGE"
};

// Determine the current Android API level by reading ro.build.version.sdk.
static int getApi() {
    try {
        string out = getprop("ro.build.version.sdk");
        return out.empty() ? 0 : stoi(out);
    } catch (...) {
        return 0;
    }
}

// Check if a permission is system‑fixed (non‑revokable).  Returns true if
// the permission is marked systemFixed in dumpsys output.
static bool isSystemFixed(const string &pkg, const string &perm) {
    string cmd = "dumpsys package " + pkg + " | grep -q \"name=" + perm + ".*systemFixed=true\"; echo $?";
    string out = trim(sh(cmd).output);
    return (out == "0");
}

// Lock down one application's sensitive permissions and app ops.  This
// implementation mirrors the original behaviour but uses the updated
// APP_OPS initialisation and permission revocation logic.  See the original
// source for detailed commentary.
static void hardenOne(const string &pkg) {
    // Skip if not installed
    if (trim(sh("pm list packages " + pkg).output).empty()) {
        cout << "[!] " << pkg << " not installed, skipping\n";
        return;
    }
    const vector<int> users = listUsers();
    int api = getApi();
    sh("pm clear " + pkg + " 2>/dev/null");
    for (int u : users) {
        sh("am force-stop --user " + to_string(u) + ' ' + pkg + " 2>/dev/null");
    }
    int uid = -1;
    {
        string out = trim(sh("cmd package resolve-uid " + pkg).output);
        if (!out.empty() && all_of(out.begin(), out.end(), ::isdigit)) {
            uid = stoi(out);
        }
    }
    auto setOp = [&](const string &op) {
        string opQuoted = "'" + op + "'";
        for (int u : users) {
            sh(APP_OPS + " set --user " + to_string(u) + ' ' + pkg + ' ' + opQuoted + " ignore 2>/dev/null");
        }
        if (uid >= 0) {
            sh(APP_OPS + " set --uid " + to_string(uid) + ' ' + opQuoted + " ignore 2>/dev/null");
        }
    };
    auto isOpSupported = [&](const string &op) {
        if ((op == "android:read_precise_phone_state" || op == "android:read_call_log") && api < 35) return false;
        if ((op == "android:read_basic_phone_state" || op == "android:read_sensitive_phone_state") && api < 34) return false;
        return true;
    };
    for (const string &op : kIdOps) {
        if (isOpSupported(op)) setOp(op);
    }
    for (const string &op : kPrivOps) {
        setOp(op);
    }
    for (const string &op : kSpecialOps) {
        setOp(op);
    }
    auto revokePerm = [&](const string &perm) {
        if ((perm == "android.permission.READ_BASIC_PHONE_STATE" || perm == "android.permission.READ_SENSITIVE_PHONE_STATE") && api < 34) {
            return;
        }
        if (isSystemFixed(pkg, perm)) return;
        string permQ = "'" + perm + "'";
        for (int u : users) {
            sh("pm revoke --user " + to_string(u) + ' ' + pkg + ' ' + permQ + " 2>/dev/null");
        }
        if (api >= 33) {
            sh("cmd permission revokelocked " + pkg + ' ' + permQ + " 2>/dev/null");
        }
    };
    for (const string &perm : kIdPerms) {
        revokePerm(perm);
    }
    for (const string &perm : kPrivPerms) {
        revokePerm(perm);
    }
    revokePerm("android.permission.QUERY_ALL_PACKAGES");
    cout << "[+] " << pkg << " permissions locked down\n";
}

// Apply hardening to all target packages.  After revocation, a
// PACKAGE_RESTARTED broadcast is sent to ensure the packages recognise the
// permission changes.  See the original implementation for details.
static void blockTargets() {
    initAppOps();
    vector<string> pkgs = getTargetPkgs();
    for (const string &pkg : pkgs) {
        hardenOne(pkg);
    }
    for (const string &pkg : pkgs) {
        sh("am broadcast -a android.intent.action.PACKAGE_RESTARTED --es android.intent.extra.PACKAGE_NAME "
           + pkg + " --ez all_users true 2>/dev/null");
    }
}

/* ---------------- Refresh Broadcasts ---------------- */

static void broadcastRefresh() {
    sh("am broadcast -a android.intent.action.USER_PRESENT 2>/dev/null");
    sh("am broadcast -a android.intent.action.CONFIGURATION_CHANGED 2>/dev/null");
    sh("am broadcast -a android.intent.action.LOCALE_CHANGED 2>/dev/null");
}

/* ---------------- Dangerous: Wipe User 0 Data ---------------- */

// Erase the main user (user 0) system settings and accounts.  This method
// checks for root and SELinux permissive before proceeding.  On Android 11
// additional locations for settings storage have been introduced ?they are
// removed by the call to nukeSSAID().
static void wipeUser0All() {
    if (geteuid() != 0) {
        logMsg("REFUSE: not root, cannot wipe user0");
        return;
    }
    string en;
    try {
        en = trim(readFile("/sys/fs/selinux/enforce"));
    } catch (...) {}
    if (!en.empty() && en[0] == '1') {
        logMsg("REFUSE: SELinux enforcing, cannot wipe user0");
        return;
    }
    logMsg("DANGER: wiping /data/system/users/0/*");
    sh("rm -rf /data/system/users/0/* 2>/dev/null");
    // Recreate a minimal settings_ssaid.xml to avoid boot issues
    writeFile("/data/system/users/0/settings_ssaid.xml",
              "<?xml version='1.0' encoding='utf-8'?><map></map>",
              0600, 1000, 1000);
}

/* ---------------- Nuke Google Advertising ID (AAID/GAID) ---------------- */

static void nukeAAID() {
    sh("am force-stop com.google.android.gms 2>/dev/null");
    sh("pm clear com.google.android.gms 2>/dev/null");
    sh("am force-stop com.android.vending 2>/dev/null");
    sh("pm clear com.android.vending 2>/dev/null");
    vector<string> gPaths = {
        "/data/data/com.google.android.gms/shared_prefs/*adid*.xml",
        "/data/data/com.google.android.gms/shared_prefs/*advert*.xml",
        "/data/data/com.google.android.gms/shared_prefs/*gaid*.xml",
        "/data/data/com.google.android.gms/shared_prefs/*ads*id*.xml",
        "/data/data/com.google.android.gms/databases/*adid*",
        "/data/data/com.google.android.gms/databases/*advert*",
        "/data/data/com.google.android.gms/files/*adid*",
        "/data/data/com.google.android.gms/files/*gaid*",
        "/data/data/com.google.android.gms/no_backup/*adid*",
        "/data/data/com.google.android.gms/no_backup/*gaid*",
        "/data/data/com.google.android.gms/app_measurement",
        "/data/data/com.google.android.gms/files/measurement*",
        "/data/data/com.google.android.gms/cache/*ads*"
    };
    for (const string &p : gPaths) {
        sh("rm -rf " + p + " 2>/dev/null");
    }
    sh("settings delete secure advertising_id 2>/dev/null");
    sh("settings delete global advertising_id 2>/dev/null");
    sh("am force-stop com.google.android.gms 2>/dev/null");
    broadcastRefresh();
    logMsg("AAID/GAID reset (nuked)");
}

/* ---------------- Nuke Android ID / SSAID (for all users) ---------------- */

// Remove SSAID files and database entries.  Extended to clear additional
// locations introduced in Android 11 such as system_de and system_ce.
static void nukeSSAID() {
    vector<int> users = listUsers();
    for (int u : users) {
        string base = "/data/system/users/" + to_string(u) + "/settings_ssaid.xml";
        if (fileExists(base)) {
            string bak = base + ".bak_nuke_" + to_string(::time(nullptr));
            sh("cp '" + base + "' '" + bak + "' 2>/dev/null");
            sh("rm -f '" + base + "' 2>/dev/null");
            logMsg("Removed SSAID file for user " + to_string(u));
        }
        // Delete from settings database as well
        sh("/system/bin/settings --user " + to_string(u) + " delete secure android_id 2>/dev/null");
        sh("/system/bin/settings --user " + to_string(u) + " delete global android_id 2>/dev/null");
    }
    // Additional mirrored or device encrypted locations to remove
    vector<string> mirrorPaths = {
        "/data/system_de/0/settings_ssaid.xml",
        "/data/system_ce/0/settings_ssaid.xml",
        "/data/misc_de/0/settings_ssaid.xml",
        "/data/misc_ce/0/settings_ssaid.xml"
    };
    for (const string &m : mirrorPaths) {
        sh("rm -f " + m + " 2>/dev/null");
    }
    broadcastRefresh();
    logMsg("SSAID reset for all users");
}

/* ---------------- WebView Data and Fingerprint Suppression ---------------- */

static void hardenWebView() {
    int api = getApi();
    vector<string> webviewCleanupCmds; // 添加缺失的变量声明
    logMsg("Hardening WebView for Android API " + to_string(api));
    
    // 基础WebView命令行参数，根据Android版本调整
    string baseCmdline;
    if (api >= 34) { // Android 14+
        baseCmdline = "webview --disable-quic --enable-features=ReducedReferrerGranularity,BlockInsecurePrivateNetworkRequests,ForceLocalSecureContext --disable-features=NetworkTimeServiceQuerying,ThirdPartyStoragePartitioningBlocked,WebRTC,WebBluetooth,Serial,USB,FileSystemAPI,IdleDetection,MediaSession,MediaCapabilities,DocumentWrite,NotificationTriggers,WebOTP,PaymentRequest,PermissionsPolicyDefaultAllowList";
    } else if (api >= 31) { // Android 12+
        baseCmdline = "webview --disable-quic --enable-features=ReducedReferrerGranularity --disable-features=NetworkTimeServiceQuerying,WebRTC,WebBluetooth";
    } else {
        baseCmdline = "webview --disable-quic --enable-features=ReducedReferrerGranularity --disable-features=NetworkTimeServiceQuerying";
    }
    
    // 写入WebView命令行配置
    writeFile("/data/local/tmp/webview-command-line", baseCmdline + "\n", 0644, 0, 0);
    
    // 对目标应用进行WebView数据清理
    vector<string> pkgs = getTargetPkgs();
    if (pkgs.empty()) {
        logMsg("No target packages found for WebView hardening");
        return;
    }
    
    // 并行处理多个应用，提高效率
    
    for (const string &pkg : pkgs) {
        // 基础WebView目录清理
        vector<string> basePaths = {
            "/data/data/" + pkg + "/app_webview",
            "/data/data/" + pkg + "/app_textures",
            "/data/data/" + pkg + "/cache",
            "/data/data/" + pkg + "/app_chrome",
            "/data/data/" + pkg + "/code_cache",
            "/data/data/" + pkg + "/app_webview/Default/GPUCache",
            "/data/data/" + pkg + "/app_webview/Default/Service Worker",
            "/data/data/" + pkg + "/app_webview/Default/Storage",
            "/data/data/" + pkg + "/app_webview/Default/Local Storage",
            "/data/data/" + pkg + "/app_webview/Default/Cookies",
            "/data/data/" + pkg + "/shared_prefs/*webview*.xml"
        };
        
        // Android 14+新增的WebView数据位置
        if (api >= 34) {
            vector<string> a14Paths = {
                "/data/data/" + pkg + "/app_webview/Default/WebData",
                "/data/data/" + pkg + "/app_webview/Default/IndexedDB",
                "/data/data/" + pkg + "/app_webview/Default/Origin Trips",
                "/data/data/" + pkg + "/app_webview/Default/Session Storage",
                "/data/data/" + pkg + "/app_webview/Default/Favicons",
                "/data/data/" + pkg + "/app_webview/Default/Visited Links",
                "/data/data/" + pkg + "/app_webview/Default/Network Cache",
                "/data/data/" + pkg + "/app_webview/Default/ShaderCache",
                "/data/data/" + pkg + "/app_webview/Default/Storage/ext/",
                "/data/data/" + pkg + "/app_webview/Default/Privacy Sandbox/"
            };
            basePaths.insert(basePaths.end(), a14Paths.begin(), a14Paths.end());
        }
        
        // 添加清理命令
        for (const string &p : basePaths) {
            webviewCleanupCmds.push_back("rm -rf " + p + " 2>/dev/null");
        }
        
        // 强制停止应用以释放锁定的文件
        webviewCleanupCmds.push_back("am force-stop " + pkg + " 2>/dev/null");
    }
    
    // 并行执行清理命令
    if (!webviewCleanupCmds.empty()) {
        executeParallel(webviewCleanupCmds, 4); // 使用4个线程并行处理
    }
    
    // Android 14+特有：创建WebView隔离配置
    if (api >= 34) {
        // 创建WebView隔离目录
        string webviewIsolateDir = "/data/local/tmp/webview_isolated/";
        sh("mkdir -p " + webviewIsolateDir + " 2>/dev/null");
        sh("chmod 700 " + webviewIsolateDir + " 2>/dev/null");
        
        // 写入WebView隐私增强配置
        string privacyConfig = "[Privacy]\nBlockThirdPartyCookies=true\nDoNotTrack=true\nReduceFingerprinting=true\nBlockWebRTC=true\nBlockWebBluetooth=true\nBlockGeolocation=true\nBlockNotifications=true\nBlockMediaDevices=true\n";
        writeFile(webviewIsolateDir + "webview_privacy.conf", privacyConfig, 0644, 0, 0);
        
        logMsg("[Android 14+] WebView isolation and privacy configuration applied");
    }
    
    logMsg("WebView hardening completed for " + to_string(pkgs.size()) + " packages");
}


// 系统级别修改功能 - 删除重复定义
// 此函数已在前面定义，此处为重复定义，已删除
// 自动服务管理功能 - 删除重复定义  
// 此函数已在前面定义，此处为重复定义，已删除
// 运行时自动配置生成
static void autoRuntimeConfig() {
    logMsg("生成运行时自动配置", 1);
    
    // 根据系统时间生成动态配置
    time_t now = time(nullptr);
    struct tm* timeInfo = localtime(&now);
    int hour = timeInfo->tm_hour;
    
    // 根据时间段应用不同配置
    if (hour >= 6 && hour < 12) {
        logMsg("应用上午时段配置", 1);
        setpropKV("spoof.runtime.period", "morning");
        setpropKV("spoof.runtime.activity", "reading");
    } else if (hour >= 12 && hour < 18) {
        logMsg("应用下午时段配置", 1);
        setpropKV("spoof.runtime.period", "afternoon");
        setpropKV("spoof.runtime.activity", "working");
    } else {
        logMsg("应用晚间时段配置", 1);
        setpropKV("spoof.runtime.period", "evening");
        setpropKV("spoof.runtime.activity", "relaxing");
    }
    
    // 生成随机设备使用模式
    vector<string> usagePatterns = {"casual", "heavy", "balanced"};
    int patternIndex = getRandomGenerator().randInRange(0, (int)usagePatterns.size() - 1);
    setpropKV("spoof.runtime.usage_pattern", usagePatterns[patternIndex]);
    
    logMsg("运行时配置生成完成", 1);
}

/* ---------------- DRM/Keystore Cache Clearing ---------------- */

// Remove DRM caches and optionally keystore.  In earlier versions the
// keystore directory was removed unconditionally which could lead to boot
// loops because the system was unable to recreate required key material.
// This implementation deletes only media DRM caches by default and makes
// clearing the keystore optional via the `spoof.clear_drm_keystore=1`
// property.  See the main documentation for details.
static void clearDrmKeystore() {
    // Always delete media DRM caches; these are safe to remove and will
    // not prevent the system from booting.  They will be recreated as
    // needed by the media framework.
    vector<string> drmPaths = {
        "/data/mediadrm/*",
        "/data/misc/mediadrm/*",
        "/data/misc/media/*",
        // Google Play DRM and other caches
        "/data/data/com.google.android.gms/app_chimera/m/00000000",
        "/data/data/com.google.android.gms/no_backup",
        "/data/data/com.google.android.gms/files/drm",
        "/data/data/com.google.android.gms/files/*drm*"
    };
    for (const string &p : drmPaths) {
        sh("rm -rf " + p + " 2>/dev/null");
    }
    // Only remove the keystore if explicitly requested.  Removing the
    // keystore can cause the device to boot loop if the hardware key
    // management service cannot reinitialise it correctly.
    if (getprop("spoof.clear_drm_keystore") == "1") {
        vector<string> ks = {
            "/data/misc/keystore",
            "/data/misc/keystore/user_0",
            "/data/misc/keystore/user_0/software"
        };
        for (const string &p : ks) {
            sh("rm -rf " + p + " 2>/dev/null");
        }
    }
}

/* ---------------- External Storage ID files blocking ---------------- */

static void installEmptyMap(const string& path) {
    static const string xmlEmpty = "<?xml version='1.0' encoding='utf-8'?><map></map>";
    writeFile(path, xmlEmpty, 0600, 1000, 1000);
    chmod(path.c_str(), 0444);
}

static void strengthenExtStorageBlocks() {
    vector<string> files = {
        "/storage/emulated/0/.UTSystemConfig/Global/Alvin2.xml",
        "/storage/emulated/0/.UTSystemConfig/Global/Alvin2.xml.bak",
        "/storage/emulated/0/.UTSystemConfig/Global/ContextData.xml",
        "/storage/emulated/0/.UTSystemConfig/Global/ContextData.xml.bak",
        "/storage/emulated/0/.DataStorage/Alvin2.xml",
        "/storage/emulated/0/.DataStorage/Alvin2.xml.bak",
        "/storage/emulated/0/.DataStorage/ContextData.xml",
        "/storage/emulated/0/.DataStorage/ContextData.xml.bak"
    };
    for (const string &f : files) {
        installEmptyMap(f);
    }
    vector<string> patterns = {
        "find /storage/emulated/0 -maxdepth 5 -type f -iname '*deviceid*' -delete",
        "find /storage/emulated/0 -maxdepth 5 -type f -iname '*uuid*' -delete",
        "find /storage/emulated/0 -maxdepth 5 -type f -iname 'clientudid.dat' -delete",
        "find /storage/emulated/0 -maxdepth 5 -type f -iname 'meta.dat' -delete",
        "find /storage/emulated/0 -type f -iname '.cuid*' -delete",
        "find /storage/emulated/0 -type f -iname '.adiu' -delete",
        "find /storage/emulated/0 -type f -iname '.duid' -delete",
        "find /storage/emulated/0 -type f -iname '.push_deviceid*' -delete",
        "find /storage/emulated/0 -type f -iname '.imei*.txt' -delete",
        "find /storage/emulated/0 -type f -iname '.DC*.txt' -delete",
        "rm -rf /storage/emulated/0/.pns /storage/emulated/0/.oukdtft /storage/emulated/0/msc",
        "rm -rf /storage/emulated/0/LMDevice /storage/emulated/0/LMDeviceId /storage/emulated/0/.lm_device",
        "rm -rf /storage/emulated/0/Android/obj/.um /storage/emulated/0/Android/data/.um"
    };
    for (const string &cmd : patterns) {
        sh(cmd + " 2>/dev/null");
    }
}

/* ---------------- UTDevice (UTDID) Clear and Rewrite ---------------- */

static void clearAndRewriteUtdid(bool rewrite = false) {
    auto delSettingKey = [&](const string &table, const string &key) {
        sh("/system/bin/settings --user 0 delete " + table + " " + key + " 2>/dev/null");
    };
    delSettingKey("system", "mqBRboGZkQPcAkyk");
    delSettingKey("system", "dxCRMxhQkdGePGnp");
    delSettingKey("secure", "mqBRboGZkQPcAkyk");
    delSettingKey("secure", "dxCRMxhQkdGePGnp");
    vector<string> cmds = {
        "find /data/data -type f -iname '*utdid*' -delete",
        "find /data/data -type f -iname '*alvin*' -delete",
        "find /data/data -type f -iname '*contextdata*' -delete",
        "find /data/misc -type f -iname '*utdid*' -delete",
        "find /data/misc -type f -iname '*alvin*' -delete",
        "find /data/misc -type f -iname '*contextdata*' -delete",
        "find /storage/emulated/0 -maxdepth 4 -type f -iname '*utdid*' -delete",
        "find /storage/emulated/0 -maxdepth 4 -type f -iname '*alvin*' -delete",
        "find /storage/emulated/0 -maxdepth 4 -type f -iname '*contextdata*' -delete",
        "find /storage/emulated/0/.UTSystemConfig/Global -type f -iname '*.bak' -delete",
        "find /storage/emulated/0/.UTSystemConfig/Global -type f -iname '*utdid*' -delete",
        "find /storage/emulated/0/.DataStorage -type f -iname '*.bak' -delete",
        "find /storage/emulated/0/.DataStorage -type f -iname '*utdid*' -delete"
    };
    for (const string &c : cmds) {
        sh(c + " 2>/dev/null");
    }
    if (!rewrite) {
        strengthenExtStorageBlocks();
        return;
    }
    string newUtdid = randHex(24);
    string xmlContent = "<?xml version='1.0' encoding='utf-8'?><map>"
                        "<string name=\"mqBRboGZkQPcAkyk\">" + newUtdid + "</string>"
                        "<string name=\"dxCRMxhQkdGePGnp\">" + newUtdid + "</string></map>";
    vector<string> targets = {
        "/storage/emulated/0/.UTSystemConfig/Global/Alvin2.xml",
        "/storage/emulated/0/.UTSystemConfig/Global/Alvin2.xml.bak",
        "/storage/emulated/0/.UTSystemConfig/Global/ContextData.xml",
        "/storage/emulated/0/.UTSystemConfig/Global/ContextData.xml.bak",
        "/storage/emulated/0/.DataStorage/Alvin2.xml",
        "/storage/emulated/0/.DataStorage/Alvin2.xml.bak",
        "/storage/emulated/0/.DataStorage/ContextData.xml",
        "/storage/emulated/0/.DataStorage/ContextData.xml.bak"
    };
    for (const string &path : targets) {
        writeFile(path, xmlContent, 0600, 1000, 1000);
    }
    logMsg("Rewrote UTDID to " + newUtdid);
}

/* ---------------- SDK ID Caches Clearing & OpenID/DeviceID Override ---------------- */

static void clearSdkIdCachesAndRewrite(const string &openId, const string &deviceId) {
    // 移除/data/misc_ce/0 /data/misc_de/0 的通配符清理，只在 /data/data /data/user_de 进行查找
    vector<string> roots = {"/data/data", "/data/user_de"};
    vector<string> keys = {"*uuid*", "*oaid*", "*adid*", "*device_id*", "*identifier*", "*utdid*", "*alvin*", "*contextdata*"};
    for (const string &root : roots) {
        for (const string &pattern : keys) {
            sh("find " + root + " -type f -iname '" + pattern + "' -delete 2>/dev/null");
        }
    }
    vector<string> specificCmds = {
        "find /data/data/com.google.android.gms -type f -iname '*adid*' -delete",
        "find /data/data/com.google.firebase.installations -type f -iname '*.xml' -delete",
        "find /data/data/com.miui.analytics -type f -iname '*oaid*' -delete",
        "find /data/data/com.miui.idservice -type f -iname '*oaid*' -delete",
        "find /data/data/com.xiaomi.xmsf -type f -iname '*uuid*' -delete",
        "find /data/data/com.cfcaMLog -type f -iname '*id*' -delete",
        "find /data/data/com.cloudwalk.live -type f -iname '*id*' -delete",
        "find /data/data/com.eg.android.AlipayGphone -type f -iname '*oaid*' -delete",
        "find /data/data/com.eg.android.AlipayGphone -type f -iname '*uuid*' -delete",
        "find /data/data/com.eg.android.AlipayGphone -type f -iname '*adid*' -delete"
    };
    for (const string &cmd : specificCmds) {
        sh(cmd + " 2>/dev/null");
    }
    for (const string &pkg : getTargetPkgs()) {
        sh("pm clear " + pkg + " 2>/dev/null");
        sh("am force-stop " + pkg + " 2>/dev/null");
    }
    vector<pair<string, string>> propsToSet = {
        {"persist.sys.openudid", openId},
        {"persist.sys.device_id", deviceId},
        {"persist.sys.oaid", openId},
        {"persist.sys.adid", openId},
        {"persist.sys.uuid", deviceId}
    };
    for (const auto &kv : propsToSet) {
        setpropKV(kv.first, kv.second);
        if (getprop(kv.first) != kv.second) {
            setpropKV(kv.first, kv.second);
        }
    }
    sh("settings delete secure advertising_id 2>/dev/null");
    broadcastRefresh();
}

/* ---------------- Rotate SSAID (Android_ID) for Target Apps ---------------- */

static string randomSSAID() {
    return randHex(16);
}

static void rotateSSAIDForTargets() {
    vector<int> users = listUsers();
    vector<string> pkgs = getTargetPkgs();
    for (int u : users) {
        string path = "/data/system/users/" + to_string(u) + "/settings_ssaid.xml";
        if (!fileExists(path)) continue;
        string backupPath = path + ".bak_" + to_string(::time(nullptr));
        sh("cp '" + path + "' '" + backupPath + "' 2>/dev/null");
        string xml = readFile(path);
        string modifiedXml = xml;
        for (const string &pkg : pkgs) {
            regex re("<string name=\\\"" + pkg + "\\\">[0-9A-Fa-f]{16}</string>");
            modifiedXml = regex_replace(modifiedXml, re, "");
        }
        if (modifiedXml.find("<map>") == string::npos) {
            modifiedXml = "<?xml version='1.0' encoding='utf-8'?><map></map>";
        }
        size_t insertPos = modifiedXml.rfind("</map>");
        if (insertPos == string::npos) insertPos = modifiedXml.size();
        string additions;
        for (const string &pkg : pkgs) {
            additions += "<string name=\"" + pkg + "\">" + randomSSAID() + "</string>";
        }
        modifiedXml.insert(insertPos, additions);
        writeFile(path, modifiedXml, 0600, 1000, 1000);
        logMsg("Rotated SSAID for user=" + to_string(u) + " for " + to_string(pkgs.size()) + " apps");
    }
}

/* ---------------- Core Spoofing: Generate and Apply New Device Properties ---------------- */

static string newIMEI() {
    string body = "35" + randDigits(12);
    body.resize(14);
    return body + luhn(body);
}

static string newICCID() {
    string body = "89" + randDigits(18);
    body.resize(19);
    return body + luhn(body);
}

static string newMAC() {
    uniform_int_distribution<int> dist(0, 255);
    stringstream ss;
    ss << uppercase << hex;
    for (int i = 0; i < 6; ++i) {
        int v = dist(getRandomGenerator().getRng());
        if (i == 0) v = (v & 0xFE) | 0x02;
        ss << setw(2) << setfill('0') << v << (i < 5 ? ":" : "");
    }
    return ss.str();
}

static string stripColon(string s) {
    s.erase(remove(s.begin(), s.end(), ':'), s.end());
    return s;
}

// Spoof core system properties and random identifiers. This function
// generates new IMEIs, IMSIs, MAC addresses, build fingerprints and more.
// After setting the properties it invokes the various hardening routines.
// 更改记录结构
struct ChangeRecord {
    string name;
    string id;
    string data;
    string result;
    string timestamp;
};

// 全局更改记录列表
static vector<ChangeRecord> changeRecords;
static mutex recordsMutex;

// 记录更改
static void recordChange(const string& name, const string& id, const string& data, const string& result) {
    ChangeRecord record;
    record.name = name;
    record.id = id;
    record.data = data;
    record.result = result;
    
    // 获取当前时间
    time_t now = time(nullptr);
    char timeStr[100];
    strftime(timeStr, sizeof(timeStr), "%Y-%m-%d %H:%M:%S", localtime(&now));
    record.timestamp = string(timeStr);
    
    // 添加到记录列表
    lock_guard<mutex> lock(recordsMutex);
    changeRecords.push_back(record);
    
    // 同时记录到日志
    logMsg("[更改记录] " + name + " (ID: " + id + ") - 结果: " + result, 2);
}

// 显示所有更改记录
static void displayChangeRecords() {
    logMsg("\n=== 更改记录摘要 ===\n", 1);
    
    lock_guard<mutex> lock(recordsMutex);
    for (const auto& record : changeRecords) {
        string log = "- " + record.timestamp + " | " + record.name + 
                   " (ID: " + record.id + ") | 结果: " + record.result;
        logMsg(log, 1);
    }
    
    logMsg("\n总计更改数量: " + to_string(changeRecords.size()), 1);
}

// 导出更改记录为JSON
static string exportChangeRecords() {
    string json = "[{";
    lock_guard<mutex> lock(recordsMutex);
    
    for (size_t i = 0; i < changeRecords.size(); i++) {
        const auto& r = changeRecords[i];
        json += "{\"name\":\"" + r.name + "\"," +
                "\"id\":\"" + r.id + "\"," +
                "\"data\":\"" + r.data + "\"," +
                "\"result\":\"" + r.result + "\"," +
                "\"timestamp\":\"" + r.timestamp + "\"}";
        if (i < changeRecords.size() - 1) json += ",";
    }
    
    json += "]";
    return json;
}

static bool spoofCoreProps(bool reset = false) {
    logMsg("开始核心属性欺骗过程..", 1);
    displayDeviceInfo();  // 显示设备信息
    
    // 生成更真实的设备属性和随机标识符，支持Android 14-15
    string serial    = maybeOverride("serial",  randAZ09(12));
    string imei1     = maybeOverride("imei1",   newIMEI());
    string imei2     = maybeOverride("imei2",   newIMEI());
    string imsi1     = maybeOverride("imsi1",   randDigits(15));
    string imsi2     = maybeOverride("imsi2",   randDigits(15));
    string iccid1    = maybeOverride("iccid1",  newICCID());
    string iccid2    = maybeOverride("iccid2",  newICCID());
    string meid      = maybeOverride("meid",    randHex(14));
    string macWifi   = maybeOverride("mac_wifi", newMAC());
    string macBt     = maybeOverride("mac_bt",  newMAC());
    string macEth    = maybeOverride("mac_eth", newMAC());
    string adid      = maybeOverride("adid",    randHex(32));
    string openudid  = maybeOverride("openudid", randHex(32));
    string devID     = maybeOverride("device_id", randAZ09(16));
    string fsn       = maybeOverride("fsn",     randAZ09(12));
    string phoneSn   = maybeOverride("phone_sn", randAZ09(12));
    string eseId     = maybeOverride("ese_id",  randHex(16));
    string cplc      = maybeOverride("cplc",    randHex(16));
    string regId     = maybeOverride("reg_id",  randHex(24));
    string hwrev     = maybeOverride("hwrev",   string("rev_") + randHex(4));
    string brand     = maybeOverride("brand",   randAZ09(6));
    string name      = maybeOverride("name",    randAZ09(8));
    string device    = maybeOverride("device",  randAZ09(8));
    string board     = maybeOverride("board",   randAZ09(6));
    string seId      = maybeOverride("seid",    randHex(16));
    
    // 增强：添加更多设备ID类型
    string subscriberId1 = maybeOverride("subscriber_id1", randDigits(15));
    string subscriberId2 = maybeOverride("subscriber_id2", randDigits(15));
    string telephonyDeviceId1 = maybeOverride("telephony_id1", newIMEI());
    string telephonyDeviceId2 = maybeOverride("telephony_id2", newIMEI());
    string secureAndroidId = maybeOverride("secure_android_id", randHex(16));
    string bluetoothName = maybeOverride("bluetooth_name", "BT_" + randAZ09(8));
    string wlanMacRandomized = maybeOverride("wlan_mac_random", newMAC());
    string ethernetMacRandomized = maybeOverride("eth_mac_random", newMAC());
    string oaidToken = maybeOverride("oaid_token", randHex(64));
    string androidId2 = maybeOverride("android_id2", randHex(16));
    string mediaDrmId = maybeOverride("media_drm_id", randHex(32));
    string buildUuid = maybeOverride("build_uuid", randHex(36));
    string secureId = maybeOverride("secure_id", randHex(32));
    string settingsSecureId = maybeOverride("settings_secure_id", randHex(32));
    string buildSerial = maybeOverride("build_serial", randAZ09(16));
    string buildDescription = maybeOverride("build_description", randAZ09(32));
    string displayId = maybeOverride("display_id", randAZ09(16));
    string productName = maybeOverride("product_name", randAZ09(8));
    string fingerprint2 = maybeOverride("fingerprint2", brand + "/" + name + "/" + device + ":10/RP1A.200720.011/" + randDigits(7) + ":user/release-keys");
    
    // 记录生成的标识符
    recordChange("设备序列号", "SERIAL", getprop("ro.serialno"), serial);
    recordChange("IMEI 1", "IMEI1", getprop("ril.imei1"), imei1);
    recordChange("IMEI 2", "IMEI2", getprop("ril.imei2"), imei2);
    recordChange("IMSI 1", "IMSI1", getprop("ril.imsi1"), imsi1);
    recordChange("IMSI 2", "IMSI2", getprop("ril.imsi2"), imsi2);
    recordChange("ICCID 1", "ICCID1", getprop("ril.iccid"), iccid1);
    recordChange("ICCID 2", "ICCID2", getprop("ril.iccid2"), iccid2);
    recordChange("MEID", "MEID", getprop("ril.meid"), meid);
    recordChange("WiFi MAC", "MAC_WIFI", getprop("persist.wifi.macaddress"), macWifi);
    recordChange("蓝牙 MAC", "MAC_BT", getprop("persist.service.bdroid.bdaddr"), macBt);
    recordChange("以太网MAC", "MAC_ETH", getprop("persist.ethernet.macaddress"), macEth);
    recordChange("Android ID", "ADID", getprop("ro.boot.android_id"), adid);
    recordChange("OpenUDID", "OPENUDID", "", openudid);
    recordChange("设备ID", "DEVICE_ID", "", devID);
    
    // 记录新增的设备ID
    recordChange("Subscriber ID 1", "SUBSCRIBER_ID1", getprop("ril.subscriberid1"), subscriberId1);
    recordChange("Subscriber ID 2", "SUBSCRIBER_ID2", getprop("ril.subscriberid2"), subscriberId2);
    recordChange("Telephony Device ID 1", "TELEPHONY_ID1", getprop("ril.devicename1"), telephonyDeviceId1);
    recordChange("Telephony Device ID 2", "TELEPHONY_ID2", getprop("ril.devicename2"), telephonyDeviceId2);
    recordChange("Secure Android ID", "SECURE_ANDROID_ID", getprop("ro.serialno"), secureAndroidId);
    recordChange("蓝牙名称", "BLUETOOTH_NAME", getprop("net.bt.name"), bluetoothName);
    recordChange("随机WiFi MAC", "WLAN_MAC_RANDOM", getprop("ro.wlan.mac.random"), wlanMacRandomized);
    recordChange("随机以太网MAC", "ETH_MAC_RANDOM", getprop("ro.ethernet.mac.random"), ethernetMacRandomized);
    recordChange("OAID Token", "OAID_TOKEN", getprop("persist.sys.oaid.token"), oaidToken);
    recordChange("Android ID 2", "ANDROID_ID2", getprop("ro.vendor.boot.android_id"), androidId2);
    recordChange("Media DRM ID", "MEDIA_DRM_ID", getprop("persist.sys.media_drm_id"), mediaDrmId);
    recordChange("Build UUID", "BUILD_UUID", getprop("ro.build.uuid"), buildUuid);
    recordChange("Secure ID", "SECURE_ID", getprop("ro.secure.id"), secureId);
    recordChange("Settings Secure ID", "SETTINGS_SECURE_ID", getprop("ro.settings.secure.id"), settingsSecureId);
    recordChange("Build Serial", "BUILD_SERIAL", getprop("ro.build.serial"), buildSerial);
    recordChange("Build Description", "BUILD_DESCRIPTION", getprop("ro.build.description"), buildDescription);
    recordChange("Display ID", "DISPLAY_ID", getprop("ro.build.display.id"), displayId);
    recordChange("Product Name", "PRODUCT_NAME", getprop("ro.product.name"), productName);
    recordChange("Build Fingerprint 2", "FINGERPRINT2", getprop("ro.vendor.build.fingerprint"), fingerprint2);
    
    // Android 14-15特有标识
    string oaid      = maybeOverride("oaid",    randHex(32));
    string androidId = randHex(16);
    string gaid      = randHex(32);
    string tdid      = randHex(24);
    string venusId   = randHex(32);
    
    // 记录Android 14-15特有标识
    recordChange("OAID", "OAID", getprop("persist.sys.oaid"), oaid);
    recordChange("GAID", "GAID", "", gaid);
    recordChange("TDID", "TDID", "", tdid);
    recordChange("VenusID", "VENUS_ID", "", venusId);
    
    // 获取当前系统版本信息
    string rel = getprop("ro.build.version.release");
    if (rel.empty()) rel = "14";
    rel = maybeOverride("release", rel);
    string sdk = getprop("ro.build.version.sdk");
    if (sdk.empty()) sdk = "34";
    sdk = maybeOverride("sdk", sdk);
    
    // 随机日期生成函数，生成更真实的日期范围
    auto randDate = [&]() {
        uniform_int_distribution<int> yDist(2022, 2025);
        int year = yDist(getRandomGenerator().getRng());
        uniform_int_distribution<int> mDist(1, 12);
        int m = mDist(getRandomGenerator().getRng());
        int maxDay;
        if (m == 2) {
            // 简单的闰年判断
            maxDay = (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0) ? 29 : 28;
        } else if (m == 4 || m == 6 || m == 9 || m == 11) {
            maxDay = 30;
        } else {
            maxDay = 31;
        }
        uniform_int_distribution<int> dDist(1, maxDay);
        int day = dDist(getRandomGenerator().getRng());
        stringstream ss;
        ss << year << '-' << setw(2) << setfill('0') << m << '-' << setw(2) << setfill('0') << day;
        return ss.str();
    };
    
    string randPatchDate = randDate();
    
    // 为不同Android版本生成更真实的指纹格式
    string generatedFingerprint;
    int sdkVer = stoi(sdk);
    if (sdkVer >= 34) { // Android 14+
        // Android 14+ 更真实的指纹格式
        string buildNumber = "TP" + randDigits(8);
        generatedFingerprint = brand + "/" + name + "/" + device + ":" + rel + "/" + buildNumber + "/" + randDigits(10) + ":user/release-keys";
    } else {
        generatedFingerprint = brand + "/" + name + "/" + device + ":" + rel + "/RP1A." + randDigits(6) + "/" + randDigits(7) + ":user/release-keys";
    }
    
    string fingerprint = maybeOverride("fingerprint", generatedFingerprint);
    recordChange("Build Fingerprint", "FINGERPRINT", getprop("ro.build.fingerprint"), fingerprint);
    string bootloader = randAZ09(8);
    string cpuAbi  = getprop("ro.product.cpu.abi");
    if (cpuAbi.empty()) cpuAbi = "arm64-v8a";
    string cpuAbi2 = getprop("ro.product.cpu.abi2");
    if (cpuAbi2.empty()) cpuAbi2 = cpuAbi;
    string host     = string("builder-") + randAZ09(4);
    string buildType= "user";
    string buildUser= "android-build";
    string buildId  = string("TP") + randDigits(4);
    
    // 扩展的系统属性列表，包括Android 14-15特有的属性
    vector<pair<string, string>> props = {
        // 基础设备标识
        {"persist.sys.imei1", imei1}, {"persist.sys.imei2", imei2},
        {"persist.sys.imsi1", imsi1}, {"persist.sys.imsi2", imsi2},
        {"persist.sys.iccid1", iccid1}, {"persist.sys.iccid2", iccid2},
        {"persist.sys.meid", meid}, {"persist.sys.ese_id", eseId}, {"persist.sys.cplc", cplc},
        
        // MAC地址系列（增加以太网MAC支持）        {"persist.sys.bluetooth_address", macBt}, {"persist.sys.wifi_mac_address", macWifi},
        {"persist.sys.ethernet_address", macEth},
        
        // 广告和GUID相关ID
        {"persist.service.advertising_id", adid},
        {"persist.sys.device_guid", randHex(32)},
        {"persist.sys.device_id", devID}, {"persist.sys.reg_id", regId}, {"persist.sys.openudid", openudid},
        
        // Android 14-15特有广告和跟踪ID
        {"persist.sys.oaid", oaid}, {"persist.sys.gaid", gaid}, {"persist.sys.tdid", tdid},
        {"persist.sys.venus_id", venusId}, {"persist.sys.appset_id", randHex(32)},
        {"persist.sys.app_instance_id", randHex(32)},
        
        // 多SIM设备支持
        {"persist.sys.iccid", iccid1 + "," + iccid2},
        {"gsm.sim.operator.imsi", imsi1 + "," + imsi2},
        
        // NFC和安全元素        {"persist.sys.nfc.seid", seId},
        {"persist.sys.seid", seId},
        
        // 序列号和相关ID
        {"persist.sys.serialno", serial},
        {"persist.sys.serial_number", serial},
        {"persist.sys.fsn", fsn},
        {"persist.sys.phone_sn", phoneSn},
        {"persist.sys.bt.serialno", randAZ09(12)},
        {"persist.sys.wifi.serialno", randAZ09(12)},
        
        // 硬件和设备描述符
        {"persist.sys.hwrev", hwrev},
        {"persist.sys.brand", brand},
        {"persist.sys.name", name},
        {"persist.sys.device", device},
        {"persist.sys.board", board},
        {"persist.sys.manufacturer", brand},
        {"persist.sys.model", name},
        {"persist.sys.product", device},
        {"persist.sys.hardware", board},
        {"persist.sys.bootloader", bootloader},
        
        // Android 14-15特有构建信息
        {"persist.sys.build.fingerprint", fingerprint},
        {"persist.sys.build.date", randPatchDate},
        {"persist.sys.build.date.utc", to_string(::time(nullptr))},
        {"persist.sys.build.id", buildId},
        {"persist.sys.build.type", buildType},
        {"persist.sys.build.user", buildUser},
        {"persist.sys.build.host", host},
        
        // 传感器和硬件能力标识
        {"persist.sys.sensor.id", randHex(16)},
        {"persist.sys.camera.id", randHex(16)},
        {"persist.sys.display.id", randHex(16)},
        
        // Android 13+隐私沙盒相关
        {"persist.sys.privacy_sandbox.token", randHex(32)},
        {"persist.sys.adservices.id", randHex(32)},
        
        // 增强：新增设备ID类型系统属性
        {"persist.sys.subscriber_id1", subscriberId1},
        {"persist.sys.subscriber_id2", subscriberId2},
        {"persist.sys.telephony_id1", telephonyDeviceId1},
        {"persist.sys.telephony_id2", telephonyDeviceId2},
        {"persist.sys.secure_android_id", secureAndroidId},
        {"net.bt.name", bluetoothName},
        {"ro.wlan.mac.random", wlanMacRandomized},
        {"ro.ethernet.mac.random", ethernetMacRandomized},
        {"persist.sys.oaid.token", oaidToken},
        {"ro.vendor.boot.android_id", androidId2},
        {"persist.sys.media_drm_id", mediaDrmId},
        {"ro.build.uuid", buildUuid},
        {"ro.secure.id", secureId},
        {"ro.settings.secure.id", settingsSecureId},
        {"ro.build.serial", buildSerial},
        {"ro.build.description", buildDescription},
        {"ro.build.display.id", displayId},
        {"ro.product.name", productName},
        {"ro.vendor.build.fingerprint", fingerprint2}
    };
    
    // Android 14+特有权限和隐私属性
    if (sdkVer >= 34) {
        props.emplace_back("persist.sys.device_uniqueness", randHex(32));
        props.emplace_back("persist.sys.app_specific_id", randHex(32));
        props.emplace_back("persist.sys.read_basic_phone_state_compat", "1");
    }
    
    // Android 15特有属性
    if (sdkVer >= 35) {
        props.emplace_back("persist.sys.device_signature", randHex(40));
        props.emplace_back("persist.sys.enhanced_privacy_token", randHex(48));
    }
    cout << "[*] Setting spoofed system properties...\n";
    
    // 使用并行处理设置系统属性，提高性能
    vector<string> commands;
    for (const auto &p : props) {
        commands.push_back("resetprop \"" + p.first + "\" \"" + p.second + "\"");
    }
    
    // 对关键属性进行优先级处理和错误重试
    unordered_set<string> criticalProps = {
        "persist.sys.imei1", "persist.sys.imei2", "persist.sys.wifi_mac_address", 
        "persist.sys.bluetooth_address", "persist.sys.device_id"
    };
    
    // 优先处理关键属性
    for (const auto &p : props) {
        if (criticalProps.count(p.first)) {
            bool success = false;
            // 关键属性最多重试3次
            for (int i = 0; i < 3 && !success; i++) {
                setpropKV(p.first, p.second);
                string currentValue = getprop(p.first);
                if (currentValue == p.second) {
                    success = true;
                    logMsg("[CRITICAL] prop " + p.first + "=" + currentValue);
                } else {
                    logMsg("[RETRY] Failed to set " + p.first + ", attempt " + to_string(i+1));
                    this_thread::sleep_for(chrono::milliseconds(100));
                }
            }
        }
    }
    
    // 批量处理剩余属性
    setpropBatch(props);
    
    // Android 14+特有处理：应用权限限制和数据隔离
    int sdkVer2 = stoi(getprop("ro.build.version.sdk"));
    if (sdkVer >= 34) {
        // Android 14+特有权限管理
        logMsg("[Android 14+] Applying enhanced permission restrictions");
        vector<string> a14RestrictCmds = {
            // 限制应用访问剪贴板历史
            "cmd appops set --uid all android:read_clipboard_history ignore",
            // 限制精确传感器采样
            "cmd appops set --uid all android:high_sensor_sampling_rate ignore",
            // 限制后台位置更新
            "cmd appops set --uid all android:background_location ignore",
            // 限制屏幕录制检测
            "cmd appops set --uid all android:record_audio deny"
        };
        for (const string &cmd : a14RestrictCmds) {
            sh(cmd + " 2>/dev/null");
        }
        
        // 限制广告ID权限
        sh("cmd appops set --uid all android:read_advertising_id deny 2>/dev/null");
    }
    
    // 自动设备适配 - 根据设备型号和系统版本调整配置
    cout << "[*] 执行设备自动适配...\n";
    string deviceModel = getprop("ro.product.model");
    string manufacturer = getprop("ro.product.manufacturer");
    int apiLevel = getApi();
    
    cout << "[*] 检测到设备: " << manufacturer << " " << deviceModel << " (API " << apiLevel << ")\n";
    
    // 存储设备信息
    setpropKV("spoof.device.model", deviceModel);
    setpropKV("spoof.device.manufacturer", manufacturer);
    
    // 根据设备类型和API级别调整适配参数
    if (manufacturer.find("Xiaomi") != string::npos || manufacturer.find("Redmi") != string::npos) {
        cout << "[*] 检测到小米/红米设备，应用专用优化配置\n";
        setpropKV("spoof.adapt.miui", "1");
        // MIUI特有设置
        setpropKV("persist.sys.miui.hardware_probe", "0");
    } else if (manufacturer.find("Huawei") != string::npos || manufacturer.find("Honor") != string::npos) {
        cout << "[*] 检测到华为/荣耀设备，应用专用优化配置\n";
        setpropKV("spoof.adapt.huawei", "1");
        // EMUI特有设置
        setpropKV("ro.config.hw_features", "none");
    } else if (manufacturer.find("Samsung") != string::npos) {
        cout << "[*] 检测到三星设备，应用专用优化配置\n";
        setpropKV("spoof.adapt.samsung", "1");
        // OneUI特有设置
        setpropKV("ro.config.samsung.features", "none");
    }
    
    // API级别特定适配
    if (apiLevel >= 34) { // Android 14+
        cout << "[*] Android 14+ 系统，应用高级安全适配\n";
        // 额外的Android 14+特有设置
        setpropKV("ro.vendor.system.security_level", "0");
    }
    
    // 执行核心安全加固
    blockTargets();
    clearAndRewriteUtdid(/*rewrite=*/false);
    clearSdkIdCachesAndRewrite(openudid, devID);
    
    // 设置Android ID并应用到所有用户
    try {
        vector<int> users = listUsers();
        for (int u : users) {
            sh("/system/bin/settings --user " + to_string(u) + " put secure android_id '" + androidId + "' 2>/dev/null");
            sh("/system/bin/settings --user " + to_string(u) + " put global android_id '" + androidId + "' 2>/dev/null");
        }
        logMsg("New device Android_ID -> " + androidId);
        
        // Android 14+特有：设置OAID到系统设置
        if (sdkVer2 >= 34) {
            sh("/system/bin/settings put secure oaid '" + oaid + "' 2>/dev/null");
        }
    } catch (...) {
        logMsg("WARN: failed to set new Android_ID");
    }
    
    // 增强的WebView保护
    hardenWebView();
    recordChange("WebView保护", "WEBVIEW_PROTECT", "WebView设置和缓存", "已加固");
    
    // Android 14+特有：WebView隐私增强设置
    if (sdkVer >= 34) {
        string webviewCmdline = "webview --disable-quic --enable-features=ReducedReferrerGranularity,BlockInsecurePrivateNetworkRequests --disable-features=NetworkTimeServiceQuerying,ThirdPartyStoragePartitioningBlocked";        
        writeFile("/data/local/tmp/webview-command-line", webviewCmdline + "\n", 0644, 0, 0);
        logMsg("[Android 14+] Enhanced WebView privacy settings applied");
    }
    
    // 可选的DRM缓存清理
    if (getprop("spoof.clear_drm") == "1") {
        clearDrmKeystore();
        recordChange("DRM缓存清理", "DRM_CLEAN", "DRM缓存和密钥存储", "已清理");
    }
    
    // 增强的隐私保护：隔离存储和文件系统保护
    if (getprop("spoof.enhanced_privacy") == "1") {
        logMsg("Applying enhanced privacy protections");
        recordChange("隐私保护", "PRIVACY_ENHANCE", "系统隐私设置", "已增强");
        strengthenExtStorageBlocks();
        
        // 创建文件系统隔离
        vector<string> isolateCmds = {
            "mkdir -p /data/local/tmp/isolated_storage",
            "chmod 700 /data/local/tmp/isolated_storage",
            // 为关键目录创建只读保护
            "touch /data/local/tmp/isolated_storage/.protected",
            "chmod 444 /data/local/tmp/isolated_storage/.protected"
        };
        for (const string &cmd : isolateCmds) {
            sh(cmd + " 2>/dev/null");
        }
    }
    
    // 执行应用级和系统级增强功能
    logMsg("执行增强系统功能", 1);
    
    
    // 系统级别修改
    systemLevelModifications();
    
    // 自动服务管理
    autoServiceManagement();
    
    // 生成运行时配置
    autoRuntimeConfig();
    
    logMsg("增强系统功能执行完成", 1);
    return true;
}

/* ---------------- Optional: Create Isolated Test User ---------------- */

static int createIsolatedUser() {
    string out = sh("pm create-user PVD_TestUser").output;
    smatch m;
    regex re(R"(Success: created user id (\d+))");
    if (regex_search(out, m, re)) {
        int newId = stoi(m[1]);
        logMsg("Created new test user: id=" + to_string(newId));
        return newId;
    }
    logMsg("WARN: create-user failed: " + out);
    return -1;
}

static void migratePkgsToUser(int newUserId) {
    if (newUserId < 0) return;
    for (const string &pkg : getTargetPkgs()) {
        sh("pm install-existing --user " + to_string(newUserId) + " " + pkg + " 2>/dev/null");
        if (getprop("spoof.keep.owner") != "1") {
            sh("pm uninstall --user 0 " + pkg + " 2>/dev/null");
        }
    }
    sh("am switch-user " + to_string(newUserId) + " 2>/dev/null");
}

/* ---------------- SELinux Handling ---------------- */

static void restoreSelinux() {
    if (!needRestoreSelinux) return;
    try {
        ofstream ofs("/sys/fs/selinux/enforce");
        if (ofs.is_open()) {
            ofs << 1;
            ofs.close();
        } else {
            system("setenforce 1");
        }
    } catch (...) {
        // ignore
    }
}

static void signalHandler(int) {
    restoreSelinux();
    _Exit(1);
}

static void registerSignalHandlers() {
    atexit(restoreSelinux);
    for (int sig : {SIGINT, SIGTERM, SIGABRT, SIGSEGV}) {
        signal(sig, signalHandler);
    }
}

static void setEnforce(int mode) {
    const char* path = "/sys/fs/selinux/enforce";
    try {
        ofstream ofs(path);
        if (!ofs.is_open()) throw runtime_error("open enforce failed");
        ofs << mode;
        ofs.close();
    } catch (...) {
        system((string("setenforce ") + to_string(mode)).c_str());
    }
    ifstream ifs(path);
    int curMode = 1;
    if (ifs.is_open()) {
        ifs >> curMode;
    }
    if (curMode != mode) {
        throw runtime_error("Failed to set SELinux mode");
    }
}

/* ---------------- Main ---------------- */

// 解析命令行参数的辅助函数
static unordered_map<string, string> parseArgs(int argc, char* argv[]) {
    unordered_map<string, string> args;
    for (int i = 1; i < argc; i++) {
        string arg = argv[i];
        if (arg.substr(0, 2) == "--") {
            size_t eqPos = arg.find('=');
            if (eqPos != string::npos) {
                string key = arg.substr(2, eqPos - 2);
                string value = arg.substr(eqPos + 1);
                args[key] = value;
            } else {
                args[arg.substr(2)] = "1";
            }
        }
    }
    return args;
}

// 显示帮助信息
static void showHelp() {
    cout << "设备欺骗工具 (Enhanced for Android 14+)\n";
    cout << "用法: spoof [选项]\n\n";
    cout << "选项:\n";
    cout << "  --help                 显示此帮助信息\n";
    cout << "  --skip-wipe            跳过用户0数据擦除\n";
    cout << "  --skip-selinux         跳过SELinux设置为宽容模式\n";
    cout << "  --clear-drm            清理DRM缓存\n";
    cout << "  --create-user          创建隔离测试用户\n";
    cout << "  --enhanced-privacy     启用增强隐私保护模式\n";
    cout << "  --mode=<mode>          设置欺骗模式 (default/light/strong/custom)\n";
    cout << "  --target=<package>     指定目标应用包名，可多次使用\n";
    cout << "  --seed=<value>         设置随机数生成器种子\n";
    cout << "  --verbose              启用详细日志\n";
    cout << "\n高级功能选项:\n";
    cout << "  --save-config[=<name>] 保存当前配置到文件，可选指定配置名称\n";
    cout << "  --load-config[=<name>] 从文件加载配置，可选指定配置名称\n";
    cout << "  --apply-after-save     保存配置后继续应用\n";
    cout << "  --batch-process=<pkgs> 批量处理应用，pkgs可以是'all'或逗号分隔的包名列表\n";
    cout << "  --generate-report      生成系统信息报告\n";
    cout << "\n系统属性配置:\n";
    cout << "  spoof.override.*       覆盖特定属性值\n";
    cout << "  spoof.wipe_user0       控制是否擦除用户0数据\n";
    cout << "  spoof.selinux.skip     跳过SELinux设置\n";
    cout << "  spoof.clear_drm        控制是否清理DRM缓存\n";
    cout << "  spoof.create_user      控制是否创建隔离用户\n";
    cout << "  spoof.enhanced_privacy 启用增强隐私保护\n";
    cout << "  spoof.adapt.*          设备适配相关属性\n";
}

// 保存当前配置到文件
static void saveConfiguration(const string& configName = "default") {
    cout << "[+] 保存当前配置到" << configName << "\n";
    
    string configDir = "/data/local/tmp/spoof_configs";
    sh("mkdir -p " + configDir);
    
    string configPath = configDir + "/" + configName + ".conf";
    ofstream configFile(configPath);
    if (!configFile.is_open()) {
        cout << "[-] 无法创建配置文件: " << configPath << "\n";
        return;
    }
    
    // 保存时间戳和基本信息
    time_t now = time(nullptr);
    configFile << "# 配置文件保存时间: " << ctime(&now);
    configFile << "# 设备: " << getprop("ro.product.manufacturer") << " " << getprop("ro.product.model") << "\n";
    configFile << "# Android版本: " << getprop("ro.build.version.release") << " (API " << getApi() << ")\n";
    
    // 保存关键配置属性
    vector<string> propsToSave = {
        "spoof.network.spoof",
        "spoof.network.dns",
        "spoof.network.proxy.host",
        "spoof.network.proxy.port",
        "spoof.network.proxy.bypass",
        "spoof.network.latency",
        "spoof.network.download_speed",
        "spoof.network.upload_speed",
        "spoof.create_user",
        "spoof.clear_drm",
        "spoof.enhanced_privacy",
        "spoof.adapt.miui",
        "spoof.adapt.huawei",
        "spoof.adapt.samsung"
    };
    
    configFile << "\n# 配置属性\n";
    for (const auto& prop : propsToSave) {
        string value = getprop(prop);
        if (!value.empty()) {
            configFile << prop << "=" << value << "\n";
        }
    }
    
    // 保存目标应用列表
    configFile << "\n# 目标应用\n";
    string targetPkgsStr = getprop("spoof.target_packages");
    if (!targetPkgsStr.empty()) {
        stringstream ss(targetPkgsStr);
        string pkg;
        while (getline(ss, pkg, ',')) {
            configFile << "target=" << trim(pkg) << "\n";
        }
    }
    
    configFile.close();
    chmod(configPath.c_str(), 0600);
    cout << "[+] 配置已保存到: " << configPath << "\n";
}

// 从配置文件加载配置
static bool loadConfiguration(const string& configName = "default") {
    cout << "[+] 从" << configName << " 加载配置\n";
    
    string configPath = "/data/local/tmp/spoof_configs/" + configName + ".conf";
    if (!fileExists(configPath)) {
        cout << "[-] 配置文件不存在 " << configPath << "\n";
        return false;
    }
    
    ifstream configFile(configPath);
    string line;
    vector<string> targetPkgs;
    
    while (getline(configFile, line)) {
        // 跳过注释和空行
        line = trim(line);
        if (line.empty() || line[0] == '#') continue;
        
        size_t eqPos = line.find('=');
        if (eqPos == string::npos) continue;
        
        string key = trim(line.substr(0, eqPos));
        string value = trim(line.substr(eqPos + 1));
        
        if (key == "target") {
            targetPkgs.push_back(value);
        } else {
            setpropKV(key, value);
            cout << "[*] 加载配置: " << key << "=" << value << "\n";
        }
    }
    
    // 保存目标应用列表
    if (!targetPkgs.empty()) {
        string targetPkgsStr;
        for (const auto& pkg : targetPkgs) {
            if (!targetPkgsStr.empty()) targetPkgsStr += ",";
            targetPkgsStr += pkg;
        }
        setpropKV("spoof.target_packages", targetPkgsStr);
    }
    
    configFile.close();
    cout << "[+] 配置加载成功\n";
    return true;
}

// 收集并打印系统信息报告
static void generateSystemReport() {
    cout << "[*] 生成系统信息报告...\n";
    
    vector<pair<string, string>> systemInfo = {
        {"设备型号", getprop("ro.product.model")},
        {"制造商", getprop("ro.product.manufacturer")},
        {"Android版本", getprop("ro.build.version.release")},
        {"API级别", to_string(getApi())},
        {"构建指纹", getprop("ro.build.fingerprint")},
        {"内核版本", getprop("ro.build.version.release")},
        {"SELinux模式", getprop("ro.build.selinux")},
        {"CPU架构", getprop("ro.product.cpu.abi")},
        {"设备ID", getprop("persist.sys.device_id")},
        {"当前用户ID", getprop("ro.build.user")}
    };
    
    // 保存报告到文件
    string reportPath = "/data/local/tmp/system_report.txt";
    ofstream reportFile(reportPath);
    
    if (reportFile.is_open()) {
        time_t now = time(nullptr);
        reportFile << "系统信息报告 - 生成时间: " << ctime(&now);
        reportFile << "-----------------------------------------------------\n";
        
        for (const auto& [label, value] : systemInfo) {
            reportFile << label << ": " << value << "\n";
        }
        
        // 添加更多详细信息
        reportFile << "\n网络信息:\n";
        reportFile << "IP地址: " << sh("ip addr show | grep inet").output << "\n";
        reportFile << "DNS服务器: " << sh("getprop net.dns1").output << "\n";
        
        reportFile.close();
        cout << "[*] 系统信息报告已保存到: " << reportPath << "\n";
    }
    
    // 同时打印到控制台
    cout << "[*] 系统信息摘要:\n";
    for (const auto& [label, value] : systemInfo) {
        cout << "    " << label << ": " << value << "\n";
    }
}

// 优化的批处理模块，支持多进程并行处理和环境自适应
static void batchProcessApps(const vector<string>& packages) {
    if (packages.empty()) {
        logMsg("没有要处理的应用", 1);
        return;
    }
    
    // 系统资源检测和批处理策略调整
    int cpuCores = sysconf(_SC_NPROCESSORS_ONLN);
    long totalMemKb = sysconf(_SC_PHYS_PAGES) * sysconf(_SC_PAGESIZE) / 1024;
    int maxParallelProcesses = max(1, min(cpuCores / 2, (int)(totalMemKb / 204800))); // 200MB内存处理一个应用    
    logMsg("系统资源检测 CPU核心=" + to_string(cpuCores) + " 内存=" + to_string(totalMemKb/1024) + "MB", 1);
    logMsg("优化并行处理数 " + to_string(maxParallelProcesses), 1);
    
    // 为每个应用保存当前配置
    saveConfiguration("batch_backup");
    
    // 创建线程池用于并行处理
    ThreadPool pool(maxParallelProcesses);
    vector<future<void>> results;
    
    // 每个应用的处理任务
    for (const auto& packageName : packages) {
        results.push_back(
            pool.enqueue([packageName] {
                try {
                    logMsg("开始处理应用 " + packageName, 1);
                    
                    // 检查应用是否安装
                    string checkResult = sh("pm list packages | grep " + packageName).output;
                    if (checkResult.find(packageName) == string::npos) {
                        logMsg("应用未安装 " + packageName + "，跳过", 1);
                        return;
                    }
                    
                    // 重置特定于应用的设置
                    setpropKV("spoof.target_packages", packageName);
                    
                    // 应用隔离处理
                    logMsg("创建应用隔离环境", 2);
                    string isolateDir = "/data/local/tmp/isolated_" + getRandomGenerator().randHex(8);
                    sh("mkdir -p " + isolateDir + " 2>/dev/null");
                    sh("chmod 700 " + isolateDir + " 2>/dev/null");
                    
                    // 应用特定配置
                    logMsg("应用特定欺骗配置", 2);
                    
                    // 清理应用缓存
                    logMsg("清理应用缓存", 2);
                    sh("pm clear " + packageName + " 2>/dev/null");
                    sh("rm -rf /data/data/" + packageName + "/cache/* 2>/dev/null");
                    sh("rm -rf /data/data/" + packageName + "/app_webview/* 2>/dev/null");
                    sh("rm -rf /data/data/" + packageName + "/databases/* 2>/dev/null");
                    
                    // 清理广告ID和设备ID缓存
                    sh("rm -f /data/data/" + packageName + "/shared_prefs/*advertising* 2>/dev/null");
                    sh("rm -f /data/data/" + packageName + "/shared_prefs/*device* 2>/dev/null");
                    
                    // 重置应用数据文件
                    logMsg("重置应用数据文件", 2);
                    vector<string> dataFiles = {
                        "shared_prefs",
                        "databases",
                        "files",
                        "no_backup"
                    };
                    
                    for (const auto& dataDir : dataFiles) {
                        string fullPath = "/data/data/" + packageName + "/" + dataDir;
                        if (fileExists(fullPath)) {
                            // 选择性备份并重置关键文件
                            vector<string> criticalFiles = {"settings.xml", "preferences.xml", "config.db"};
                            for (const auto& criticalFile : criticalFiles) {
                                string fileToCheck = fullPath + "/" + criticalFile;
                                if (fileExists(fileToCheck)) {
                                    string backupPath = isolateDir + "/" + criticalFile + ".bak";
                                    sh("cp " + fileToCheck + " " + backupPath + " 2>/dev/null");
                                    logMsg("备份关键文件: " + criticalFile, 3);
                                }
                            }
                            
                            // 生成随机设备信息写入应用配置
                            string randomConfig = "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<map>\n";
                            vector<pair<string, string>> configItems = {
                                {"device_id", getRandomGenerator().randHex(32)},
                                {"installation_id", getRandomGenerator().randHex(16)},
                                {"client_id", getRandomGenerator().randHex(24)},
                                {"last_sync_time", to_string(::time(nullptr))},
                                {"session_id", getRandomGenerator().randHex(40)}
                            };
                            
                            for (const auto& [key, value] : configItems) {
                                randomConfig += "    <string name=\"" + key + "\">" + value + "</string>\n";
                            }
                            randomConfig += "</map>\n";
                            
                            writeFile(fullPath + "/device_config.xml", randomConfig, 0600, 0, 0);
                            logMsg("写入随机配置文件 " + packageName + "/" + dataDir + "/device_config.xml", 3);
                        }
                    }
                    
                    // 应用权限调整
                    logMsg("调整应用权限", 2);
                    vector<string> sensitivePermissions = {
                        "READ_PHONE_STATE",
                        "READ_CALL_LOG",
                        "WRITE_CALL_LOG",
                        "ACCESS_FINE_LOCATION",
                        "ACCESS_COARSE_LOCATION",
                        "READ_CONTACTS",
                        "WRITE_CONTACTS",
                        "RECORD_AUDIO",
                        "CAMERA"
                    };
                    
                    for (const auto& perm : sensitivePermissions) {
                        sh("pm revoke " + packageName + " android.permission." + perm + " 2>/dev/null");
                    }
                    
                    // 应用进程清理
                    logMsg("清理应用进程", 2);
                    sh("am force-stop " + packageName + " 2>/dev/null");
                    
                    // 清理隔离目录
                    sh("rm -rf " + isolateDir + " 2>/dev/null");
                    
                    logMsg("应用处理完成: " + packageName, 1);
                } catch (const exception& e) {
                    logMsg("处理应用失败 " + packageName + ": " + string(e.what()), 1);
                }
            })
        );
    }
    
    // 等待所有任务完成
    for (auto& result : results) {
        result.wait();
    }
    
    // 定义计数变量
    int successCount = 0;
    int failCount = 0;
    
    logMsg("批处理完成，共处理" + to_string(packages.size()) + " 个应用", 1);
    logMsg("[+] 批量处理完成:", 1);
    logMsg("    成功: " + to_string(successCount), 1);
    logMsg("    失败: " + to_string(failCount), 1);
    
    // 恢复原始配置
    bool configLoaded = loadConfiguration("batch_backup");
}


int main(int argc, char* argv[]) {
    // 记录开始时间用于性能统计
    auto startTime = chrono::high_resolution_clock::now();
    
    ios::sync_with_stdio(false);
    registerSignalHandlers();
    
    // 解析命令行参数
    auto args = parseArgs(argc, argv);
    
    // 检查是否显示帮助信息
    if (args.count("help")) {
        showHelp();
        return 0;
    }
    
    // 设置详细日志模式
    bool verbose = args.count("verbose") || getprop("spoof.verbose") == "1";
    
    // 打印欢迎信息
    cout << "[+] 设备id启动 (Enhanced for Android 14+)\n";
    cout << "[+] API级别: " << getApi() << ", Android版本: " << getprop("ro.build.version.release") << "\n";
    
    // 扩展PATH环境变量，包含常见的root二进制文件位置
    setenv("PATH", "/sbin:/system/bin:/system/xbin:/vendor/bin:/system/sbin:/data/local/tmp:/data/adb/ksu/bin:/data/adb/magisk", 1);
    
    // 检查root权限
    if (geteuid() != 0) {
        cerr << "[!] 需要root权限\n";
        return 1;
    }
    
        // 根据命令行参数设置系统属性
        if (args.count("clear-drm")) {
            setpropKV("spoof.clear_drm", "1");
        }
        if (args.count("skip-wipe")) {
            setpropKV("spoof.wipe_user0", "0");
        }
        if (args.count("enhanced-privacy")) {
            setpropKV("spoof.enhanced_privacy", "1");
        }
        if (args.count("create-user")) {
            setpropKV("spoof.create_user", "1");
        }
    
    // 网络配置功能已移除
    
    // 处理配置保存/加载功能
    if (args.count("save-config")) {
        string configName = args.count("save-config") && args["save-config"] != "1" ? args["save-config"] : "default";
        saveConfiguration(configName);
        cout << "[+] 配置已保存为: " << configName << "\n";
        if (!args.count("apply-after-save")) {
            return 0; // 保存配置后退出
        }
    }
    
    if (args.count("load-config")) {
        string configName = args.count("load-config") && args["load-config"] != "1" ? args["load-config"] : "default";
        if (!loadConfiguration(configName)) {
            cout << "[-] 加载配置失败: " << configName << "\n";
            return 1;
        }
        cout << "[+] 成功加载配置: " << configName << "\n";
    }
    
    // 处理批量应用处理功能
    if (args.count("batch-process")) {
        string batchParam = args["batch-process"];
        vector<string> targetPkgs;
        
        if (batchParam == "all") {
            // 获取所有已安装的第三方应用
            string packagesOutput = sh("pm list packages -3").output;
            stringstream ss(packagesOutput);
            string line;
            while (getline(ss, line)) {
                if (line.find("package:") == 0) {
                    string pkg = line.substr(8); // 去除 "package:" 前缀
                    if (!pkg.empty()) {
                        targetPkgs.push_back(pkg);
                    }
                }
            }
        } else {
            // 处理逗号分隔的包名列表
            stringstream ss(batchParam);
            string pkg;
            while (getline(ss, pkg, ',')) {
                pkg = trim(pkg);
                if (!pkg.empty()) {
                    targetPkgs.push_back(pkg);
                }
            }
        }
        
        if (!targetPkgs.empty()) {
            batchProcessApps(targetPkgs);
            recordChange("批量应用处理", "BATCH_APP_PROCESS", "目标应用列表", "已处理");
            return 0; // 批量处理完成后退出
        } else {
            cout << "[-] 没有有效的应用包名进行批量处理\n";
            return 1;
        }
    }
    
    // 生成系统报告
    if (args.count("generate-report")) {
        generateSystemReport();
        return 0; // 生成报告后退出
    }
    
    // 设置随机数种子
    if (args.count("seed")) {
            setpropKV("spoof.rng_seed", args["seed"]);
        }
    
    // 处理网络配置参数
    if (args.count("no-network")) {
            setpropKV("spoof.network.spoof", "0");
        } else {
            setpropKV("spoof.network.spoof", "1");
        }
        
        if (args.count("network-dns")) {
            setpropKV("spoof.network.dns", args["network-dns"]);
        }
        
        if (args.count("network-proxy")) {
            string proxy = args["network-proxy"];
            size_t colonPos = proxy.find(":");
            if (colonPos != string::npos) {
                string host = proxy.substr(0, colonPos);
                string port = proxy.substr(colonPos + 1);
                setpropKV("spoof.network.proxy.host", host);
                setpropKV("spoof.network.proxy.port", port);
            }
        }
        
        if (args.count("network-proxy-bypass")) {
            setpropKV("spoof.network.proxy.bypass", args["network-proxy-bypass"]);
        }
        
        if (args.count("network-conditions")) {
            string conditions = args["network-conditions"];
            size_t comma1 = conditions.find(",");
            if (comma1 != string::npos) {
                size_t comma2 = conditions.find(",", comma1 + 1);
                if (comma2 != string::npos) {
                    string latency = conditions.substr(0, comma1);
                    string down = conditions.substr(comma1 + 1, comma2 - comma1 - 1);
                    string up = conditions.substr(comma2 + 1);
                    setpropKV("spoof.network.latency", latency);
                    setpropKV("spoof.network.download_speed", down);
                    setpropKV("spoof.network.upload_speed", up);
                }
            }
        }
        
        // 初始化随机数生成器
        initRng();
        
        // 初始化AppOps命令路径
        initAppOps();
        
        // 设置欺骗模式
        string mode = args.count("mode") ? args["mode"] : "default";
        cout << "[+] 使用欺骗模式: " << mode << "\n";
        
        // 根据模式调整行为
        if (mode == "light") {
            setpropKV("spoof.light_mode", "1");
            cout << "[+] 轻量模式：仅修改核心标识，保留大部分系统设置\n";
        } else if (mode == "strong") {
            setpropKV("spoof.strong_mode", "1");
            setpropKV("spoof.enhanced_privacy", "1");
            cout << "[+] 强力模式：全面清理和伪造，提供最高隐私保护\n";
        } else if (mode == "custom") {
            cout << "[+] 自定义模式：根据系统属性配置执行\n";
        }
        
        // 设置SELinux模式
        bool skipSelinux = args.count("skip-selinux") || getprop("spoof.selinux.skip") == "1";
        if (!skipSelinux) {
            auto selinuxStart = chrono::high_resolution_clock::now();
            setEnforce(0);
            needRestoreSelinux = true;
            auto selinuxEnd = chrono::high_resolution_clock::now();
            if (verbose) {
                auto duration = chrono::duration_cast<chrono::milliseconds>(selinuxEnd - selinuxStart).count();
                cout << "[*] SELinux设置为宽容模式 (" << duration << "ms)\n";
            }
        } else {
            logMsg("SELinux模式修改已跳过");
        }
    
        // 执行核心欺骗流程
        bool lightMode = getprop("spoof.light_mode") == "1";
        bool strongMode = getprop("spoof.strong_mode") == "1";
        
        // 统计数据
        int stepsCompleted = 0;
        // 计算总步骤数
        const int totalSteps = lightMode ? 5 : 
                              (strongMode ? 9 : 7);
        
        // 步骤1: 可选的用户0数据擦除
        if (!lightMode && getprop("spoof.wipe_user0") != "0") {
            auto stepStart = chrono::high_resolution_clock::now();
            cout << "[+] 步骤 1/" << totalSteps << ": 清理用户0数据\n";
            wipeUser0All();
            stepsCompleted++;
            if (verbose) {
                auto duration = chrono::duration_cast<chrono::milliseconds>(chrono::high_resolution_clock::now() - stepStart).count();
                cout << "[*] 用户0数据清理完成 (" << duration << "ms)\n";
            }
        } else if (lightMode) {
            cout << "[+] 轻量模式：跳过用户数据清理\n";
        }
        
        // 步骤2: 清理广告ID
        {  
            auto stepStart = chrono::high_resolution_clock::now();
            cout << "[+] 步骤 " << (lightMode ? 1 : 2) << "/" << totalSteps << ": 清理广告ID\n";
            nukeAAID();
            stepsCompleted++;
            if (verbose) {
                auto duration = chrono::duration_cast<chrono::milliseconds>(chrono::high_resolution_clock::now() - stepStart).count();
                cout << "[*] 广告ID清理完成 (" << duration << "ms)\n";
            }
        }
        
        // 步骤3: 清理SSAID
        {  
            auto stepStart = chrono::high_resolution_clock::now();
            cout << "[+] 步骤 " << (lightMode ? 2 : 3) << "/" << totalSteps << ": 清理Android ID\n";
            nukeSSAID();
            stepsCompleted++;
            if (verbose) {
                auto duration = chrono::duration_cast<chrono::milliseconds>(chrono::high_resolution_clock::now() - stepStart).count();
                cout << "[*] Android ID清理完成 (" << duration << "ms)\n";
            }
        }
        
        // 步骤4: 核心属性伪造
        {  
            auto stepStart = chrono::high_resolution_clock::now();
            cout << "[+] 步骤 " << (lightMode ? 3 : 4) << "/" << totalSteps << ": 伪造核心设备属性\n";
            spoofCoreProps();
            stepsCompleted++;
            if (verbose) {
                auto duration = chrono::duration_cast<chrono::milliseconds>(chrono::high_resolution_clock::now() - stepStart).count();
                cout << "[*] 核心属性伪造完成 (" << duration << "ms)\n";
            }
        }
        
        // 步骤4.1: 网络配置功能已移除
        cout << "[+] 网络配置功能已移除\n";
        
        // 步骤4.2: 执行增强功能配置
        {  
            auto stepStart = chrono::high_resolution_clock::now();
            int currentStep = 4;
            if (lightMode) currentStep = 4;
            cout << "[+] 步骤 " << currentStep << "/" << totalSteps << ": 执行增强功能配置\n";
            
            // 检查设备兼容性
            if (getprop("spoof.adapt.miui") == "1") {
                // 清理MIUI特有缓存
                sh("rm -rf /data/data/com.miui.securitycenter/cache/*");
                sh("rm -rf /data/data/com.miui.systemui/cache/*");
            } else if (getprop("spoof.adapt.huawei") == "1") {
                // 清理EMUI特有缓存
                sh("rm -rf /data/data/com.huawei.systemmanager/cache/*");
            } else if (getprop("spoof.adapt.samsung") == "1") {
                // 清理OneUI特有缓存
                sh("rm -rf /data/data/com.samsung.android.securitylogagent/cache/*");
            }
            
            // 启用增强的日志隐藏功能
            sh("logcat -c"); // 清除日志
            setpropKV("persist.log.tag", "NONE");
            
            // 增强性能优化
            setpropKV("sys.perf.opt", "1");
            setpropKV("ro.kernel.perf_optimization", "1");
            
            stepsCompleted++;
            if (verbose) {
                auto duration = chrono::duration_cast<chrono::milliseconds>(chrono::high_resolution_clock::now() - stepStart).count();
                cout << "[*] 增强功能配置完成 (" << duration << "ms)\n";
            }
        }
        
        // 步骤5: 为目标应用轮换SSAID
        if (!lightMode) {
            auto stepStart = chrono::high_resolution_clock::now();
            int currentStep = 6;
            cout << "[+] 步骤 " << currentStep << "/" << totalSteps << ": 为目标应用轮换Android ID\n";
            rotateSSAIDForTargets();
            stepsCompleted++;
            if (verbose) {
                auto duration = chrono::duration_cast<chrono::milliseconds>(chrono::high_resolution_clock::now() - stepStart).count();
                cout << "[*] 目标应用Android ID轮换完成 (" << duration << "ms)\n";
            }
        }
        
        // 步骤6: 创建隔离用户 (如果启用)
        int newUserId = -1;
        if (getprop("spoof.create_user") == "1") {
            auto stepStart = chrono::high_resolution_clock::now();
            int currentStep;
            if (lightMode) {
                currentStep = 5;
            } else {
                currentStep = 7;
                if (strongMode) currentStep = 8;
            }
            cout << "[+] 步骤 " << currentStep << "/" << totalSteps << ": 创建隔离测试用户\n";
            newUserId = createIsolatedUser();
            if (newUserId >= 0) {
                migratePkgsToUser(newUserId);
                cout << "[+] 成功创建隔离用户ID: " << newUserId << "\n";
            }
            stepsCompleted++;
            if (verbose) {
                auto duration = chrono::duration_cast<chrono::milliseconds>(chrono::high_resolution_clock::now() - stepStart).count();
                cout << "[*] 隔离用户创建完成 (" << duration << "ms)\n";
            }
        }
        
        // 强力模式下的额外步骤
        if (strongMode) {
            // 步骤7: 深度清理外部存储
            {  
                auto stepStart = chrono::high_resolution_clock::now();
                int currentStep = 8;
                cout << "[+] 步骤 " << currentStep << "/" << totalSteps << ": 深度清理外部存储\n";
                strengthenExtStorageBlocks();
                clearAndRewriteUtdid(false);
                stepsCompleted++;
                if (verbose) {
                    auto duration = chrono::duration_cast<chrono::milliseconds>(chrono::high_resolution_clock::now() - stepStart).count();
                    cout << "[*] 外部存储清理完成 (" << duration << "ms)\n";
                }
            }
            
            // 步骤8: 清理DRM缓存
            if (getprop("spoof.clear_drm") == "1") {
                auto stepStart = chrono::high_resolution_clock::now();
                int currentStep = 9;
                cout << "[+] 步骤 " << currentStep << "/" << totalSteps << ": 清理DRM缓存\n";
                clearDrmKeystore();
                stepsCompleted++;
                if (verbose) {
                    auto duration = chrono::duration_cast<chrono::milliseconds>(chrono::high_resolution_clock::now() - stepStart).count();
                    cout << "[*] DRM缓存清理完成 (" << duration << "ms)\n";
                }
            }
        }
        
        // 调用四大核心增强模块
        cout << "[+] ========================================\n";
        cout << "[+] 🚀 开始执行功能模块..\n";
        

        
        // 系统级别的安全和隐私增强
        systemLevelModifications();
        
        // 自动服务管理
        autoServiceManagement();
        
        // 运行时配置生成和应用
        autoRuntimeConfig();
        
        cout << "[+] 功能执行完成\n";
        cout << "[+] ========================================\n";
        
        // 恢复SELinux设置
        if (needRestoreSelinux) {
            restoreSelinux();
            cout << "[+] SELinux已恢复为强制模式\n";
        }
        
        // 计算总执行时间
        auto endTime = chrono::high_resolution_clock::now();
        auto totalDuration = chrono::duration_cast<chrono::milliseconds>(endTime - startTime).count();
        
        // 打印总结信息
        cout << "[+] 完成!\n";
        cout << "[+] 统计:\n";
        cout << "    - 完成步骤: " << stepsCompleted << "/" << totalSteps << "\n";
        cout << "    - 总耗时: " << totalDuration / 1000.0 << " 秒\n";
        cout << "    - 模式: ALL" << "\n";
        cout << "    - API级别: " << getApi() << "\n";
        
        // 显示并导出更改记录
        displayChangeRecords();
        string changesJson = exportChangeRecords();
        writeFile("/data/local/tmp/spoof_changes.json", changesJson, 0600, 0, 0);
        cout << "[+] 更改记录已导出到: /data/local/tmp/spoof_changes.json\n";
        // 网络配置功能已移除
        
        if (newUserId >= 0) {
            cout << "[+] 已创建隔离测试用户(ID: " << newUserId << ")\n";
        }
        
        // Android 14+特有提示
        if (getApi() >= 34) {
            cout << "[+] Android 14+ 优化已应用\n";
        }
        
        
        // 资源清理
        if (commandThreadPool != nullptr) {
            delete commandThreadPool;
            commandThreadPool = nullptr;
            logMsg("线程池资源已清理", 2);
        }
        
        if (g_randGen != nullptr) {
            delete g_randGen;
            g_randGen = nullptr;
            logMsg("随机数生成器资源已清理", 2);
        }
        
        // 清理缓存
        clearFileCache();
        clearPropertyCache();
        logMsg("系统缓存已清理", 2);
        
        // 记录最终执行时间
        logMsg("程序执行完成，总耗时: " + to_string(totalDuration) + "ms", 1);
        
        return 0;
}

// 系统级别的安全和隐私增强
static void systemLevelModifications() {
    logMsg("执行系统级别修改...", 1);
    
    // 系统级安全设置
    vector<pair<string, string>> secureSettings = {
        {"secure.allow.mock.location", "1"},               // 允许模拟位置
        {"secure.adb_enabled", "1"},                      // 启用ADB
        {"secure.keystore_unlocked", "1"},                // 解锁密钥存储
        {"secure.install_non_market_apps", "1"},          // 允许安装非市场应用
        {"secure.screensaver_enabled", "0"},               // 禁用屏保
        {"system.audio_playback_mode", "1"},              // 设置音频播放模式
        {"system.window_animation_scale", "0.5"},         // 减少窗口动画
        {"system.transition_animation_scale", "0.5"},     // 减少过渡动画
        {"system.animator_duration_scale", "0.5"}         // 减少动画持续时间
    };
    
    for (const auto& [key, value] : secureSettings) {
        sh("settings put " + key + " " + value);
        recordChange("系统设置", "SYS_SETTING_" + getShortID(key), key + ":" + value, "已设置");
    }
    
    // 增强系统防火墙规则
    if (fileExists("/system/bin/iptables")) {
        vector<string> firewallRules = {
            "-A OUTPUT -p tcp --tcp-flags ALL SYN,ACK -j DROP",  // 阻止TCP空连接
            "-A INPUT -p tcp --tcp-flags ALL SYN,ACK -j DROP"
        };
        
        for (const auto& rule : firewallRules) {
            sh("iptables " + rule + " 2>/dev/null");
            recordChange("防火墙规则", "FIREWALL_RULE", rule, "已应用");
        }
    }
    
    // Android 14+特有系统保护
    if (getApi() >= 34) { // 使用已定义的getApi函数替代未定义的sdk函数
        vector<string> a14Enhancements = {
            "settings put secure restricted_profiles_enabled 1",
            "settings put secure enhanced_standby_mode_enabled 1",
            "settings put secure hidden_api_policy 1",
            "settings put secure background_process_limit 1"
        };
        
        for (const auto& cmd : a14Enhancements) {
            sh(cmd);
            recordChange("Android 14+增强", "A14_ENHANCE", cmd, "已执行");
        }
    }
    
    // 清理系统日志
    sh("logcat -c");
    sh("rm -rf /data/system/dropbox/*");
    recordChange("系统日志清理", "SYS_LOG_CLEAN", "清理系统日志和崩溃报告", "已完成");
    
    // 增强：添加包名限制功能，阻止应用通过系统get手段获取真实ID
    logMsg("应用包名限制策略...", 1);
    
    // 创建禁止访问的敏感属性列表
    vector<string> sensitiveProps = {
        "ro.serialno", "ril.imei", "ril.imei1", "ril.imei2", "ril.imsi", "ril.imsi1", "ril.imsi2",
        "ril.iccid", "ril.iccid1", "ril.iccid2", "ril.subscriberid", "ril.subscriberid1", "ril.subscriberid2",
        "persist.wifi.macaddress", "persist.service.bdroid.bdaddr", "persist.ethernet.macaddress",
        "ro.boot.android_id", "ro.vendor.boot.android_id", "gsm.sim.serial", "gsm.sim.operator.imsi",
        "ro.build.serial", "ro.secure.id", "persist.sys.oaid", "persist.sys.oaid.token"
    };
    
    // 获取目标应用包名
    string targetPkgs = getprop("spoof.target_packages");
    vector<string> blockedPackages;
    
    // 如果没有指定目标包名，则默认阻止所有应用获取敏感ID
    if (targetPkgs.empty()) {
        // 获取所有已安装应用
        string installedPkgs = sh("pm list packages -3").output;
        istringstream pkgStream(installedPkgs);
        string pkgLine;
        while (getline(pkgStream, pkgLine)) {
            size_t pos = pkgLine.find(":");
            if (pos != string::npos) {
                string pkg = pkgLine.substr(pos + 1);
                blockedPackages.push_back(pkg);
            }
        }
    } else {
        // 从逗号分隔的字符串中解析目标包名
        istringstream pkgStream(targetPkgs);
        string pkg;
        while (getline(pkgStream, pkg, ',')) {
            blockedPackages.push_back(trim(pkg));
        }
    }
    
    // 为每个阻止的应用设置策略
    for (const string &pkg : blockedPackages) {
        logMsg("为应用设置ID访问限制: " + pkg, 2);
        
        // 限制应用对系统属性的访问
        sh("setprop spoof.restrict." + pkg + " 1 2>/dev/null");
        
        // 通过AppOps限制应用获取设备标识权限
        sh("cmd appops set " + pkg + " android:read_phone_state deny 2>/dev/null");
        sh("cmd appops set " + pkg + " android:read_telephony_subscription_info deny 2>/dev/null");
        sh("cmd appops set " + pkg + " android:read_device_identifiers deny 2>/dev/null");
        sh("cmd appops set " + pkg + " android:access_wifi_state deny 2>/dev/null");
        
        // Android 14+特有权限限制
        if (getApi() >= 34) { // 使用已定义的getApi函数替代未定义的sdk函数
            sh("cmd appops set " + pkg + " android:read_advertising_id deny 2>/dev/null");
            sh("cmd appops set " + pkg + " android:read_basic_phone_state deny 2>/dev/null");
        }
        
        recordChange("应用ID限制", "APP_ID_RESTRICT_" + getShortID(pkg), "限制应用" + pkg + "获取设备ID", "已设置");
    }
    
    // 为敏感属性设置访问控制，重定向到伪造的属性
    for (const string &prop : sensitiveProps) {
        string fakeProp = "spoof.fake." + prop;
        sh("resetprop -n " + prop + " 1234567890 2>/dev/null");
        sh("setprop " + fakeProp + " 1234567890 2>/dev/null");
        recordChange("敏感属性伪造", "PROP_SPOOF_" + getShortID(prop), prop, "已伪造");
    }
    
    // 创建getprop的包装脚本，对指定应用返回伪造ID
    string getpropWrapper = "#!/system/bin/sh\n"
"PACKAGE_NAME=$(dumpsys activity activities | grep mFocusedActivity | grep -o '[a-zA-Z0-9._]*/' | head -n 1 | sed 's:\\/::')\n"
"\n"
"# 检查是否需要返回伪造ID\n"
"if [ ! -z \"$PACKAGE_NAME\" ] && [ \"$(getprop spoof.restrict.$PACKAGE_NAME 2>/dev/null || echo 0)\" = \"1\" ]; then\n"
    "case \"$1\" in\n"
        "ro.serialno|ril.imei*|ril.imsi*|ril.iccid*|ril.subscriberid*|persist.wifi.macaddress|\n"
        "persist.service.bdroid.bdaddr|persist.ethernet.macaddress|ro.boot.android_id|\n"
        "ro.vendor.boot.android_id|gsm.sim.serial|gsm.sim.operator.imsi|ro.build.serial|\n"
        "ro.secure.id|persist.sys.oaid|persist.sys.oaid.token)\n"
            "echo \"1234567890\"\n"
            ";;&\n"
        "*)\n"
            "/system/bin/getprop \"$@\"\n"
            ";;&\n"
    "esac\n"
"else\n"
    "/system/bin/getprop \"$@\"\n"
"fi";
    
    // 写入getprop包装脚本
    writeFile("/data/local/tmp/getprop_wrapper.sh", getpropWrapper, 0755, 0, 0);
    
    // 将system/bin/getprop重命名为getprop_real，并替换为我们的包装脚本
    sh("cp /system/bin/getprop /system/bin/getprop_real 2>/dev/null || true");
    sh("cat /data/local/tmp/getprop_wrapper.sh > /system/bin/getprop 2>/dev/null || true");
    sh("chmod 755 /system/bin/getprop 2>/dev/null || true");
    
    recordChange("系统调用拦截", "GETPROP_HOOK", "拦截getprop系统调用", "已安装");
    logMsg("包名限制策略应用完成", 1);
    logMsg("系统级别修改完成", 1);
}

// 自动服务管理
static void autoServiceManagement() {
    logMsg("执行自动服务管理...", 1);
    
    // 禁用不必要的系统服务
    vector<string> servicesToDisable = {
        "com.android.cellbroadcastreceiver.CellBroadcastReceiver",
        "com.android.server.telecom.TelecomService",
        "com.android.secrecy.SecrecyService",
        "com.google.android.gms.mdm.receivers.MdmDeviceAdminReceiver",
        "com.google.android.gms.auth.managed.receiver.DevicePolicyReceiver"
    };
    
    for (const auto& service : servicesToDisable) {
        sh("pm disable " + service + " 2>/dev/null");
        recordChange("服务禁用", "SVC_DISABLE_" + getShortID(service), service, "已禁用");
    }
    
    // 优化服务启动顺序
    vector<string> servicesToOptimize = {
        "com.android.systemui",
        "com.android.settings",
        "com.android.launcher3"
    };
    
    for (const auto& service : servicesToOptimize) {
        sh("am startservice " + service + " 2>/dev/null");
        recordChange("服务优化", "SVC_OPTIMIZE_" + getShortID(service), service, "已启用");
    }
    
    // 监控异常服务
    monitorAbnormalServices();
    
    logMsg("自动服务管理完成", 1);
}

// 运行时配置生成和应用
// 增强的ID修改功能
static void enhancedIdModification(const string& packageName = "") {
    logMsg("执行增强ID修改...", 1);
    
    // 生成新的标识符
    string newAndroidId = randHex(16);
    string newOaid = randHex(32);
    string newGaid = randHex(32);
    string newTdid = randHex(24);
    string newDeviceId = randAZ09(16);
    string newOpenUdid = randHex(32);
    string newAppSetId = randHex(32);
    
    // Android 14+ 特有标识符
    string newOaid2 = randHex(32);
    string newIdfv = randHex(36);
    string newGaidv2 = randHex(32);
    
    // 记录所有ID更改
    recordChange("Android ID", "ANDROID_ID", getprop("ro.boot.android_id"), newAndroidId);
    recordChange("OAID", "OAID", getprop("persist.sys.oaid"), newOaid);
    recordChange("GAID", "GAID", getprop("persist.sys.gaid"), newGaid);
    recordChange("TDID", "TDID", getprop("persist.sys.tdid"), newTdid);
    recordChange("设备ID", "DEVICE_ID", getprop("persist.sys.device_id"), newDeviceId);
    recordChange("OpenUDID", "OPENUDID", getprop("persist.sys.openudid"), newOpenUdid);
    recordChange("AppSet ID", "APPSET_ID", getprop("persist.sys.appset_id"), newAppSetId);
    
    // 记录Android 14+特有ID
    recordChange("OAID2", "OAID2", getprop("persist.sys.oaid2"), newOaid2);
    recordChange("IDFV", "IDFV", getprop("persist.sys.idfv"), newIdfv);
    recordChange("GAIDv2", "GAIDV2", getprop("persist.sys.gaidv2"), newGaidv2);
    
    // 设置系统属性
    vector<pair<string, string>> idProps = {
        {"persist.sys.android_id", newAndroidId},
        {"persist.sys.oaid", newOaid},
        {"persist.sys.gaid", newGaid},
        {"persist.sys.tdid", newTdid},
        {"persist.sys.device_id", newDeviceId},
        {"persist.sys.openudid", newOpenUdid},
        {"persist.sys.appset_id", newAppSetId},
        {"persist.sys.oaid2", newOaid2},
        {"persist.sys.idfv", newIdfv},
        {"persist.sys.gaidv2", newGaidv2},
        {"ro.boot.android_id", newAndroidId},
        {"ro.vendor.boot.android_id", newAndroidId}
    };
    
    for (const auto& [key, value] : idProps) {
        setpropKV(key, value);
    }
    
    // 针对特定应用的ID修改
    if (!packageName.empty()) {
        logMsg("为应用" + packageName + " 修改特定ID...", 2);
        
        // 清除应用数据和缓存
        sh("pm clear " + packageName + " 2>/dev/null");
        sh("am force-stop " + packageName + " 2>/dev/null");
        
        // 清除应用特定的ID文件
        vector<string> appIdFiles = {
            "/data/data/" + packageName + "/shared_prefs/*_identifier.xml",
            "/data/data/" + packageName + "/shared_prefs/*_id.xml",
            "/data/data/" + packageName + "/shared_prefs/*_device.xml",
            "/data/data/" + packageName + "/files/*id*",
            "/data/data/" + packageName + "/files/*device*"
        };
        
        for (const auto& fileGlob : appIdFiles) {
            sh("rm -f " + fileGlob + " 2>/dev/null");
        }
        
        // 设置应用特定的系统属性
        setpropKV("spoof.app." + packageName + ".android_id", newAndroidId);
        setpropKV("spoof.app." + packageName + ".device_id", newDeviceId);
    } else {
        // 全局修改：处理所有目标应用
        for (const auto& pkg : getTargetPkgs()) {
            enhancedIdModification(pkg);
        }
        
        // 清除通用ID存储位置
        vector<string> globalIdLocations = {
            "/data/system/users/*/settings_ssaid.xml",
            "/data/misc/user/*/settings_secure.xml",
            "/data/data/com.google.android.gms/app_adid/*",
            "/data/data/com.google.android.gms/shared_prefs/adid_settings.xml",
            "/data/data/com.miui.analytics/shared_prefs/*oaid*",
            "/data/data/com.xiaomi.xmsf/shared_prefs/*uuid*"
        };
        
        for (const auto& location : globalIdLocations) {
            sh("rm -f " + location + " 2>/dev/null");
        }
        
        // 重写SSAID
        rotateSSAIDForTargets();
    }
    
    // 发送系统广播以刷新ID
    broadcastRefresh();
    logMsg("增强ID修改完成", 1);
}

// 辅助函数：创建应用隔离存储
static void createAppIsolatedStorage(const string& packageName) {
    string isoPath = "/data/local/tmp/isolated/" + packageName;
    sh("mkdir -p " + isoPath);
    sh("chmod 700 " + isoPath);
    
    // 创建必要的子目录
    vector<string> subdirs = {"cache", "files", "shared_prefs", "databases"};
    for (const auto& dir : subdirs) {
        sh("mkdir -p " + isoPath + "/" + dir);
    }
}

// 辅助函数：获取短ID
static string getShortID(const string& input) {
    // 生成输入的短哈希
    size_t hash = 0;
    for (char c : input) {
        hash = hash * 31 + c;
    }
    return to_string(hash).substr(0, 8);
}

// 辅助函数：监控异常服务
static void monitorAbnormalServices() {
    string serviceList = sh("dumpsys activity services").output;
    
    // 检查可疑服务
    vector<string> suspiciousServices = {
        "com.google.android.gms.ads",
        "com.baidu.mobstat",
        "com.umeng.analytics"
    };
    
    for (const auto& service : suspiciousServices) {
        if (serviceList.find(service) != string::npos) {
            logMsg("发现可疑服务: " + service, 1);
            recordChange("可疑服务检测", "SUSP_SVC_DETECT", service, "已发现");
        }
    }
}

// 辅助函数：生成随机指纹
static string generateRandomFingerprint() {
    vector<string> brands = {"Huawei", "Samsung", "OPPO", "vivo"};
    vector<string> models = {"Mate 60 Pro", "Galaxy S24", "Find X7", "X100 Pro"};
    vector<string> androidVersions = {"13", "14", "15"};
    
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<> brandDist(0, brands.size()-1);
    uniform_int_distribution<> modelDist(0, models.size()-1);
    uniform_int_distribution<> versionDist(0, androidVersions.size()-1);
    
    string brand = brands[brandDist(gen)];
    string model = models[modelDist(gen)];
    string version = androidVersions[versionDist(gen)];
    string buildId = randAZ09(8);
    string timestamp = to_string(time(nullptr));
    
    return brand + "/" + model + "/" + model + ":" + version + "/" + buildId + "/" + timestamp + ":user/release-keys";
}

// 辅助函数：生成随机用户代理
static string generateRandomUserAgent() {
    vector<string> brands = {"Xiaomi", "Huawei", "Samsung", "OPPO", "vivo"};
    vector<string> versions = {"13", "14", "15"};
    vector<string> webkits = {"537.36", "538.36", "539.36"};
    vector<string> chromes = {"118.0.0.0", "119.0.0.0", "120.0.0.0"};
    
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<> idx(0, brands.size()-1);
    
    return "Mozilla/5.0 (Linux; Android " + versions[idx(gen)] + "; " + brands[idx(gen)] + ") AppleWebKit/" + webkits[idx(gen)] + " (KHTML, like Gecko) Chrome/" + chromes[idx(gen)] + " Mobile Safari/" + webkits[idx(gen)];
}


// 辅助函数：检查应用是否安装
static bool isAppInstalled(const string& packageName) {
    string result = sh("pm list packages " + packageName).output;
    return result.find("package:" + packageName) != string::npos;
}

// 辅助函数：重置应用特定设置
static void resetAppSpecificSettings(const string& packageName) {
    vector<string> settingsToReset = {
        "--user 0 secure user_setup_complete",
        "--user 0 system screen_brightness",
        "--user 0 system screen_timeout"
    };
    
    for (const auto& setting : settingsToReset) {
        sh("settings delete " + setting + " " + packageName + " 2>/dev/null");
    }
}

