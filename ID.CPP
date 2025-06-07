// DeviceIdSpoofer_Enhanced_v11.cpp — Android 11-13 全量伪装（root，纯用户空间，Magisk resetprop 即刻生效）
// NDK r27

#include <array>
#include <algorithm>
#include <chrono>
#include <cctype>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <random>
#include <regex>
#include <sstream>
#include <string>
#include <vector>
#include <unistd.h>

using namespace std;
namespace fs = std::filesystem;

/* ---------- Shell 执行辅助 ---------- */
struct Exec { int st; string out; };
Exec sh(const string& cmd) {
    array<char, 4096> buf{};
    string out;
    FILE* pipe = popen((cmd + " 2>&1").c_str(), "r");
    if (!pipe) return { -1, "popen failed" };
    while (fgets(buf.data(), buf.size(), pipe)) out += buf.data();
    int status = pclose(pipe);
    return { status, out };
}
#define CHK(cmd) \
    do { auto _e = sh(cmd); if (_e.st != 0) { \
        cerr << "[ERROR] `" << cmd << "` failed: " << _e.out; exit(_e.st); } \
    } while (0)

/* ---------- 随机数生成 ---------- */
static mt19937_64 Rng([] {
    array<uint32_t,8> buf{};
    ifstream ur("/dev/urandom", ios::binary);
    if (ur.read(reinterpret_cast<char*>(buf.data()), buf.size()*4)) {
        seed_seq s(buf.begin(), buf.end());
        return mt19937_64(s);
    }
    vector<uint32_t> fb = { random_device{}(),
                            uint32_t(chrono::high_resolution_clock::now().time_since_epoch().count()),
                            uint32_t(getpid()) };
    seed_seq s2(fb.begin(), fb.end());
    return mt19937_64(s2);
}());

string randDigits(size_t n) {
    uniform_int_distribution<int> d(0,9);
    string s; while(n--) s += char('0'+d(Rng));
    return s;
}
string randHex(size_t n) {
    uniform_int_distribution<int> d(0,15);
    const char* hex="0123456789ABCDEF";
    string s; while(n--) s+=hex[d(Rng)];
    return s;
}
string randAZ09(size_t n) {
    uniform_int_distribution<int> d(0,35);
    const char* tbl="ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
    string s; while(n--) s+=tbl[d(Rng)];
    return s;
}
char luhn(const string& b) {
    int sum=0; bool alt=true;
    for(int i=int(b.size())-1;i>=0;--i){
        int v=b[i]-'0';
        if(alt){ v*=2; if(v>9) v-=9; }
        sum+=v; alt=!alt;
    }
    return char('0'+((10-sum%10)%10));
}
string newIMEI() {
    string b="35"+randDigits(12);
    b.resize(14);
    return b + luhn(b);
}
string newICCID() {
    string b="89"+randDigits(18);
    b.resize(19);
    return b + luhn(b);
}
string newMAC() {
    uniform_int_distribution<int> d(0,255);
    stringstream ss;
    for(int i=0;i<6;++i){
        int v=d(Rng);
        if(i==0) v=(v&0xFE)|0x02;
        ss<<uppercase<<hex<<setw(2)<<setfill('0')<<v;
        if(i<5) ss<<":";
    }
    return ss.str();
}
string randDate() {
    uniform_int_distribution<int> m(1,24);
    int mo=m(Rng), yr=(mo<=12?2024:2025);
    if(mo>12) mo-=12;
    int md=(mo==2?28:((mo==4||mo==6||mo==9||mo==11)?30:31));
    uniform_int_distribution<int> d(1,md);
    int da=d(Rng);
    stringstream ss;
    ss<<yr<<"-"<<setw(2)<<setfill('0')<<mo<<"-"<<setw(2)<<da;
    return ss.str();
}
string randSensor(){
    return "ACC_"+randAZ09(4)+";GYR_"+randAZ09(4)+";MAG_"+randAZ09(4);
}
string newGuid() {
    auto part=[&](int len){
        string s;
        uniform_int_distribution<int> d(0,15);
        const char* h="0123456789abcdef";
        while(len--) s+=h[d(Rng)];
        return s;
    };
    return part(8)+"-"+part(4)+"-"+part(4)+"-"+part(4)+"-"+part(12);
}
string trim(const string& s){
    auto p=s.find_last_not_of(" \t\r\n");
    return p==string::npos?"":s.substr(0,p+1);
}
string q(const string& s){ return "'"+s+"'"; }

/* ---------- 属性 & Settings ---------- */
bool setprop(const string& k,const string& v){
    return sh("resetprop -n "+q(k)+" "+q(v)).st==0;
}
bool settingsPut(int u,const string& tbl,const string& key,const string& val){
    for(int i=0;i<3;i++){
        if(sh("settings --user "+to_string(u)+" put "+tbl+" "
              +q(key)+" "+q(val)).st==0) return true;
        usleep(300000);
    }
    cerr<<"[WARN] settingsPut failed user="<<u<<" key="<<key<<"\n";
    return false;
}
vector<int> listUsers(){
    auto r=sh("pm list users").out;
    vector<int> u; regex re(R"(UserInfo\{(\d+):)");
    for(auto it=sregex_iterator(r.begin(),r.end(),re); it!=sregex_iterator(); ++it)
        u.push_back(stoi((*it)[1]));
    if(u.empty()) u.push_back(0);
    return u;
}

/* ---------- XML 补丁 ---------- */
void patchXml(const string& p,const regex& re,const string& rep){
    if(!fs::is_regular_file(p)) return;
    ifstream in(p); string t((istreambuf_iterator<char>(in)),{});
    in.close();
    ofstream out(p, ios::trunc);
    out<<regex_replace(t,re,rep);
    out.close();
    sync();
}
void patchSsaidUserkey(const string& key){
    const string p="/data/system/users/0/settings_ssaid.xml";
    if(!fs::is_regular_file(p)) return;
    ifstream in(p); string t((istreambuf_iterator<char>(in)),{});
    in.close();
    t=regex_replace(t,regex(R"((<setting[^>]+name="userkey"[^>]+value=")[^"]+)"),"$1"+key);
    t=regex_replace(t,regex(R"((<setting[^>]+name="userkey"[^>]+defaultValue=")[^"]+)"),"$1"+key);
    ofstream out(p, ios::trunc); out<<t; out.close();
    sync();
}

/* ---------- 网络 & MAC ---------- */
void applyMac(const string& m){
    sh("ip link set wlan0 down");
    sh(string("ip link set wlan0 address ")+m);
    sh("ip link set wlan0 up");
}
void restartWifi(){
    sh("svc wifi disable"); usleep(300000);
    sh("svc wifi enable");
}
void persistMac(const string& mac){
    vector<string> files={
        "/persist/wifi/WCNSS_qcom_cfg.ini",
        "/mnt/vendor/persist/wlan_mac.bin",
        "/nvdata/APCFG/APRDEB/WIFI",
        "/nvram/APCFG/APRDEB/WIFI",
        "/vendor/factory/wifi/.nvmac"
    };
    regex qcom(R"((MacAddress0=)[0-9A-F:]{17})",regex::icase);
    for(auto& f:files){
        if(!fs::is_regular_file(f)) continue;
        ifstream in(f, ios::binary);
        string buf((istreambuf_iterator<char>(in)),{});
        in.close();
        string out;
        if(f.find("WCNSS")!=string::npos){
            out=regex_replace(buf,qcom,"$1"+mac);
        } else {
            out=buf;
            auto it=out.begin();
            for(char c:mac) if(c!=':') *it++=c;
        }
        ofstream o(f, ios::binary|ios::trunc); o<<out; o.close();
        sh(string("chmod 0666 ")+f);
    }
    sync();
}

/* ---------- 清理 Firebase & DRM ---------- */
void clearFirebase(){
    for(auto& d: fs::directory_iterator("/data/data/")){
        string pref=d.path().string()+"/shared_prefs/com.google.firebase.installations.xml";
        if(fs::is_regular_file(pref)) fs::remove(pref);
    }
}
void clearMediaDrm(){
    vector<string> dirs={"/data/misc/drm","/data/misc/keystore"};
    for(auto& d:dirs){
        if(fs::exists(d)) fs::remove_all(d);
    }
}

/* ---------- UnionPay & 动态屏蔽 ---------- */
void blockUnionpay(){
    const string pkg="com.unionpay";
    for(const char* op:{"android:phone_read","android:bluetooth_scan",
        "android:coarse_location","android:fine_location",
        "android:activity_recognition","android:body_sensors"})
    {
        sh(string("appops set ")+pkg+" "+op+" ignore");
    }
    for(const char* p:{"android.permission.ACCESS_FINE_LOCATION",
        "android.permission.ACCESS_COARSE_LOCATION",
        "android.permission.BODY_SENSORS",
        "android.permission.ACTIVITY_RECOGNITION",
        "android.permission.BLUETOOTH_SCAN"})
    {
        sh(string("pm revoke ")+pkg+" "+p);
    }
    sh("pm clear com.unionpay");
}
void maskDynamic(){
    sh(R"(for f in $(find /sys /proc -type f \( -iname '*serial*' -o -iname '*mac*' \
        -o -iname '*address' -o -iname '*uid' -o -iname '*uuid' \) 2>/dev/null); do \
        mount -o bind /dev/null "$f" || chmod 000 "$f"; done)");
    sh(R"(for d in /dev/tee* /sys/class/tee /data/misc/tee /data/vendor/tee; do \
        mount -o bind /dev/null "$d" 2>/dev/null || chmod 000 "$d"; done)");
}

/* ---------- SIM & GSF 写回 ---------- */
void applySimInfo(const string& num,const string& iccid,
                  const string& imsi,const string& mcc,const string& mnc)
{
    const string db="/data/data/com.android.providers.telephony/databases/telephony.db";
    string base="sqlite3 "+db+" ";
    for(int slot=1;slot<=2;++slot){
        string where="_id="+to_string(slot);
        string sql="\"UPDATE siminfo SET "
                   "number='"+num+"',icc_id='"+iccid+"',imsi='"+imsi
                   +"',mcc_string='"+mcc+"',mnc_string='"+mnc
                   +"' WHERE "+where+";\"";
        sh(base+sql);
    }
}
void applyGsfId(const string& gsf){
    const string db="/data/data/com.google.android.gsf/databases/gservices.db";
    string cmd="sqlite3 "+db+" \"UPDATE main SET value='"+gsf
               +"' WHERE name='android_id';\"";
    sh(cmd);
}

/* ---------- 权限锁定 ---------- */
void lockPermissions(){
    sh(R"(for p in $(pm list packages -3 | cut -d: -f2); do \
         pm revoke $p android.permission.READ_PHONE_STATE; \
         pm revoke $p android.permission.READ_PHONE_NUMBERS; \
         appops set $p READ_PHONE_STATE ignore; \
         appops set $p READ_PHONE_NUMBERS ignore; \
       done)");
    sh("appops set system READ_PRIVILEGED_PHONE_STATE ignore");
}

/* ---------- 核心 spoof ---------- */
void spoof(){
    string serial=randAZ09(12), imei1=newIMEI(), imei2=newIMEI();
    string imsi1=randDigits(15), imsi2=randDigits(15);
    string iccid1=newICCID(), iccid2=newICCID();
    string meid=randHex(14), macW=newMAC(), macBt=newMAC();
    string gsf=randHex(16), aid=randHex(16), adid=randHex(32);
    string guid=newGuid(), mcc=randDigits(3), mnc=randDigits(3);
    string userkey=randHex(64), sensor=randSensor();

    // fingerprint
    string rel=trim(sh("getprop ro.build.version.release").out);
    if(rel.empty()) rel="13";
    string sdk=trim(sh("getprop ro.build.version.sdk").out);
    if(sdk.empty()) sdk="33";
    string device=randAZ09(8);
    string fp=device+"/generic/"+device+":"+rel
            +"/RP1A."+randDigits(6)
            +"/"+randDigits(7)+":user/release-keys";

    // 系统属性
    vector<pair<string,string>> props = {
        {"ro.serialno", serial},
        {"ro.product.model", device},
        {"ro.product.device", device},
        {"persist.sys.device_guid", guid},
        {"ro.build.fingerprint", fp},
        {"ro.build.version.release", rel},
        {"ro.build.version.sdk", sdk},
        {"ro.build.version.security_patch", randDate()},
        {"persist.sys.bluetooth_address", macBt},
        {"persist.service.advertising_id", adid},
        {"ro.hardware.keystore", "software"},
        {"ro.hardware.keymaster","software"},
        {"ro.keymaster.version","4"},
        {"ro.miui.cit.sensor.info", sensor},
        {"ro.boot.verifiedbootstate","green"},
        {"ro.boot.flash.locked","1"}
    };
    for(auto& kv:props) setprop(kv.first, kv.second);

    // Settings & XML
    for(int u:listUsers()){
        settingsPut(u,"secure","android_id",aid);
        settingsPut(u,"secure","ad_id",adid);
        settingsPut(u,"secure","wifi_mac_address",macW);
        settingsPut(u,"secure","bluetooth_address",macBt);
        settingsPut(u,"secure","device_guid",guid);
        patchXml("/data/system/users/"+to_string(u)+"/settings_ssaid.xml",
                 regex(R"((<setting name="android_id" value=")[^"]+)"),
                 "$1"+aid);
    }
    patchSsaidUserkey(userkey);

    // SIM & GSF
    string phone=randDigits(3)+"-"+randDigits(3)+"-"+randDigits(4);
    applySimInfo(phone,iccid1,imsi1,mcc,mnc);
    applyGsfId(gsf);

    // 清理、网络、屏蔽
    clearFirebase();
    clearMediaDrm();
    persistMac(macW);
    applyMac(macW);
    restartWifi();
    blockUnionpay();
    maskDynamic();
    lockPermissions();

    // 重启 zygote 与清日志
    sh("logcat -c");
    sh("dmesg -c > /dev/null");

    cout<<"[+] spoof finished\n";
}

/* ---------- 主入口 ---------- */
int main(){
    if(geteuid()!=0){
        cerr<<"[-] root required\n";
        return 1;
    }
    string mode=trim(sh("getenforce").out);
    sh("setenforce 0");
    spoof();
    if(mode=="Enforcing") sh("setenforce 1");
    return 0;
}
