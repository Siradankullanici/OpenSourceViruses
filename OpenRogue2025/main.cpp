// OpenRogue2025.cpp : Defines the entry point for the application.
// Upgraded version for Dev-C++ 5.11 with TDM-GCC 4.9.2 64-bit
// Demo version – Remove Malware functionality is available only in the full product.
// For full product, please contact: protonkral5668@proton.me

#include <windows.h>
#include <wininet.h>
#include <commdlg.h>   // For file open dialog
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <sys/stat.h>  // For file size checking
#include <shlobj.h>    // For folder browsing
#include <stdlib.h>
#include <tchar.h>     // For TCHAR and related functions
#include <string>

// Resource definitions (resource.h not used)
#ifndef IDS_APP_TITLE
#define IDS_APP_TITLE "OpenRogue2025"
#endif

#ifndef IDC_OPENROGUE2025
#define IDC_OPENROGUE2025 "OpenRogue2025Class"
#endif

#ifndef IDI_OPENROGUE2025
#define IDI_OPENROGUE2025 101
#endif

#ifndef IDI_SMALL
#define IDI_SMALL 102
#endif

// Control IDs for GUI elements
#define IDC_STATIC_BANNER        1001
#define IDC_STATIC_FILE          1002
#define IDC_EDIT_FILE            1003
#define IDC_BUTTON_BROWSE        1004
#define IDC_BUTTON_SCAN          1005

#define IDC_STATIC_FOLDER        1010
#define IDC_EDIT_FOLDER          1011
#define IDC_BUTTON_FOLDER_BROWSE 1012
#define IDC_BUTTON_FOLDER_SCAN   1013

// Using a list box for scan results.
#define IDC_LIST_RESULT          1006  

// New control for "Remove Malware"
#define IDC_BUTTON_REMOVE        1014

// Command ID for copying listbox text
#define IDM_COPY                 40001

#define MAX_LOADSTRING 100

// Custom messages for thread updates.
#define WM_SCAN_UPDATE (WM_USER + 1)
#define WM_SCAN_DONE   (WM_USER + 2)

// Macro definitions to simulate SEH for non-MS compilers (e.g. GCC)
#ifdef __GNUC__
#define __try try
#define __except(x) catch(...) {}
#endif

// ----------------------------
// Global Variables
// ----------------------------
HINSTANCE hInst;                    // current instance
TCHAR szTitle[MAX_LOADSTRING];      // title text
TCHAR szWindowClass[MAX_LOADSTRING];// window class name

// Global handles for our controls.
HWND hEditFile = NULL;       // File path edit control.
HWND hEditFolder = NULL;     // Folder path edit control.
HWND hListResult = NULL;     // List box for results.

volatile BOOL g_bRunning = TRUE;
HWND g_hWnd = NULL;          // Main window handle.
LONG g_ActiveThreadCount = 0; // Active scanning threads counter.

// ----------------------------
// Global Thread Handle Tracking
// ----------------------------
#define MAX_THREADS 1024
static HANDLE g_hThreadHandles[MAX_THREADS];
static int g_ThreadHandleCount = 0;
CRITICAL_SECTION g_threadLock; // Protects access to thread handles

// --------------------------
// Data structures for scanning
// --------------------------
struct QueryResult {
    char riskLevel[32];
    char virusName[64];
};

struct CacheEntry {
    char md5[33];         // MD5 hash (32 chars + null terminator)
    QueryResult result;   // Cached query result.
};

#define CACHE_SIZE 1024
static CacheEntry g_Cache[CACHE_SIZE];
static int g_CacheCount = 0;

CRITICAL_SECTION g_cacheLock;  // Protects cache access

// --------------------------
// Helper Functions
// --------------------------
void ToUpper(char* str) {
    while (*str) {
        *str = toupper(*str);
        str++;
    }
}

// SafePostMessage: Wrap PostMessage in structured exception handling
BOOL SafePostMessage(HWND hWnd, UINT msg, WPARAM wParam, LPARAM lParam)
{
    __try {
        if (hWnd && IsWindow(hWnd))
            return PostMessage(hWnd, msg, wParam, lParam);
        return FALSE;
    }
    __except(EXCEPTION_EXECUTE_HANDLER) {
        return FALSE;
    }
}

// --------------------------
// MD5 Algorithm (based on RFC 1321)
// --------------------------
typedef unsigned int uint32;

typedef struct {
    uint32 state[4];
    uint32 count[2];
    unsigned char buffer[64];
} MD5_CTX;

#define S11 7
#define S12 12
#define S13 17
#define S14 22
#define S21 5
#define S22 9
#define S23 14
#define S24 20
#define S31 4
#define S32 11
#define S33 16
#define S34 23
#define S41 6
#define S42 10
#define S43 15
#define S44 21

#define F(x, y, z) (((x) & (y)) | ((~x) & (z)))
#define G(x, y, z) (((x) & (z)) | ((y) & (~z)))
#define H(x, y, z) ((x) ^ (y) ^ (z))
#define I(x, y, z) ((y) ^ ((x) | (~z)))
#define ROTATE_LEFT(x, n) (((x) << (n)) | ((x) >> (32-(n))))

#define FF(a, b, c, d, x, s, ac) { \
 (a) += F((b), (c), (d)) + (x) + (unsigned int)(ac); \
 (a) = ROTATE_LEFT((a), (s)); \
 (a) += (b); }
#define GG(a, b, c, d, x, s, ac) { \
 (a) += G((b), (c), (d)) + (x) + (unsigned int)(ac); \
 (a) = ROTATE_LEFT((a), (s)); \
 (a) += (b); }
#define HH(a, b, c, d, x, s, ac) { \
 (a) += H((b), (c), (d)) + (x) + (unsigned int)(ac); \
 (a) = ROTATE_LEFT((a), (s)); \
 (a) += (b); }
#define II(a, b, c, d, x, s, ac) { \
 (a) += I((b), (c), (d)) + (x) + (unsigned int)(ac); \
 (a) = ROTATE_LEFT((a), (s)); \
 (a) += (b); }

void MD5Init(MD5_CTX *context)
{
    context->count[0] = context->count[1] = 0;
    context->state[0] = 0x67452301;
    context->state[1] = 0xefcdab89;
    context->state[2] = 0x98badcfe;
    context->state[3] = 0x10325476;
}

void MD5Transform(uint32 state[4], const unsigned char block[64])
{
    uint32 a, b, c, d;
    uint32 x[16];
    int i, j;
    
    a = state[0];
    b = state[1];
    c = state[2];
    d = state[3];
    
    for (i = 0, j = 0; i < 16; i++, j += 4)
         x[i] = ((uint32)block[j]) | (((uint32)block[j+1]) << 8) |
                (((uint32)block[j+2]) << 16) | (((uint32)block[j+3]) << 24);
    
    FF(a, b, c, d, x[0], S11, 0xd76aa478);
    FF(d, a, b, c, x[1], S12, 0xe8c7b756);
    FF(c, d, a, b, x[2], S13, 0x242070db);
    FF(b, c, d, a, x[3], S14, 0xc1bdceee);
    FF(a, b, c, d, x[4], S11, 0xf57c0faf);
    FF(d, a, b, c, x[5], S12, 0x4787c62a);
    FF(c, d, a, b, x[6], S13, 0xa8304613);
    FF(b, c, d, a, x[7], S14, 0xfd469501);
    FF(a, b, c, d, x[8], S11, 0x698098d8);
    FF(d, a, b, c, x[9], S12, 0x8b44f7af);
    FF(c, d, a, b, x[10], S13, 0xffff5bb1);
    FF(b, c, d, a, x[11], S14, 0x895cd7be);
    FF(a, b, c, d, x[12], S11, 0x6b901122);
    FF(d, a, b, c, x[13], S12, 0xfd987193);
    FF(c, d, a, b, x[14], S13, 0xa679438e);
    FF(b, c, d, a, x[15], S14, 0x49b40821);
    
    GG(a, b, c, d, x[1], S21, 0xf61e2562);
    GG(d, a, b, c, x[6], S22, 0xc040b340);
    GG(c, d, a, b, x[11], S23, 0x265e5a51);
    GG(b, c, d, a, x[0], S24, 0xe9b6c7aa);
    GG(a, b, c, d, x[5], S21, 0xd62f105d);
    GG(d, a, b, c, x[10], S22, 0x02441453);
    GG(c, d, a, b, x[15], S23, 0xd8a1e681);
    GG(b, c, d, a, x[4], S24, 0xe7d3fbc8);
    GG(a, b, c, d, x[9], S21, 0x21e1cde6);
    GG(d, a, b, c, x[14], S22, 0xc33707d6);
    GG(c, d, a, b, x[3], S23, 0xf4d50d87);
    GG(b, c, d, a, x[8], S24, 0x455a14ed);
    GG(a, b, c, d, x[13], S21, 0xa9e3e905);
    GG(d, a, b, c, x[2], S22, 0xfcefa3f8);
    GG(c, d, a, b, x[7], S23, 0x676f02d9);
    GG(b, c, d, a, x[12], S24, 0x8d2a4c8a);
    
    HH(a, b, c, d, x[5], S31, 0xfffa3942);
    HH(d, a, b, c, x[8], S32, 0x8771f681);
    HH(c, d, a, b, x[11], S33, 0x6d9d6122);
    HH(b, c, d, a, x[14], S34, 0xfde5380c);
    HH(a, b, c, d, x[1], S31, 0xa4beea44);
    HH(d, a, b, c, x[4], S32, 0x4bdecfa9);
    HH(c, d, a, b, x[7], S33, 0xf6bb4b60);
    HH(b, c, d, a, x[10], S34, 0xbebfbc70);
    HH(a, b, c, d, x[13], S31, 0x289b7ec6);
    HH(d, a, b, c, x[0], S32, 0xeaa127fa);
    HH(c, d, a, b, x[3], S33, 0xd4ef3085);
    HH(b, c, d, a, x[6], S34, 0x04881d05);
    HH(a, b, c, d, x[9], S31, 0xd9d4d039);
    HH(d, a, b, c, x[12], S32, 0xe6db99e5);
    HH(c, d, a, b, x[15], S33, 0x1fa27cf8);
    HH(b, c, d, a, x[2], S34, 0xc4ac5665);
    
    II(a, b, c, d, x[0], S41, 0xf4292244);
    II(d, a, b, c, x[7], S42, 0x432aff97);
    II(c, d, a, b, x[14], S43, 0xab9423a7);
    II(b, c, d, a, x[5], S44, 0xfc93a039);
    II(a, b, c, d, x[12], S41, 0x655b59c3);
    II(d, a, b, c, x[3], S42, 0x8f0ccc92);
    II(c, d, a, b, x[10], S43, 0xffeff47d);
    II(b, c, d, a, x[1], S44, 0x85845dd1);
    II(a, b, c, d, x[8], S41, 0x6fa87e4f);
    II(d, a, b, c, x[15], S42, 0xfe2ce6e0);
    II(c, d, a, b, x[6], S43, 0xa3014314);
    II(b, c, d, a, x[13], S44, 0x4e0811a1);
    II(a, b, c, d, x[4], S41, 0xf7537e82);
    II(d, a, b, c, x[11], S42, 0xbd3af235);
    II(c, d, a, b, x[2], S43, 0x2ad7d2bb);
    II(b, c, d, a, x[9], S44, 0xeb86d391);
    
    state[0] += a;
    state[1] += b;
    state[2] += c;
    state[3] += d;
}

void MD5Update(MD5_CTX *context, unsigned char *input, unsigned int inputLen)
{
    unsigned int index, partLen;
    unsigned int i;
    index = (context->count[0] >> 3) & 0x3F;
    if ((context->count[0] += inputLen << 3) < (inputLen << 3))
        context->count[1]++;
    context->count[1] += (inputLen >> 29);
    partLen = 64 - index;
    i = 0;
    if (inputLen >= partLen)
    {
        memcpy(&context->buffer[index], input, partLen);
        MD5Transform(context->state, context->buffer);
        for (i = partLen; i + 63 < inputLen; i += 64)
            MD5Transform(context->state, &input[i]);
        index = 0;
    }
    memcpy(&context->buffer[index], &input[i], inputLen - i);
}

void MD5Final(unsigned char digest[16], MD5_CTX *context)
{
    unsigned char bits[8];
    unsigned int index, padLen;
    int i;
    for (i = 0; i < 8; i++)
        bits[i] = (unsigned char)((context->count[i >> 2] >> ((i % 4) * 8)) & 0xFF);
    index = (context->count[0] >> 3) & 0x3F;
    padLen = (index < 56) ? (56 - index) : (120 - index);
    {
        unsigned char PADDING[64] = { 0x80 };
        memset(PADDING + 1, 0, 63);
        MD5Update(context, PADDING, padLen);
    }
    MD5Update(context, bits, 8);
    for (i = 0; i < 16; i++)
        digest[i] = (unsigned char)((context->state[i >> 2] >> ((i % 4) * 8)) & 0xFF);
    memset(context, 0, sizeof(*context));
}

// --------------------------
// Calculate the MD5 hash of a file.
// md5_out will contain a 33-character string (32 hex digits + null terminator).
bool CalculateFileMD5(const char* filename, char* md5_out)
{
    FILE *file = fopen(filename, "rb");
    if (!file)
        return false;
    MD5_CTX ctx;
    MD5Init(&ctx);
    {
        unsigned char buffer[1024];
        size_t bytes;
        while ((bytes = fread(buffer, 1, sizeof(buffer), file)) != 0)
        {
            MD5Update(&ctx, buffer, (unsigned int)bytes);
        }
    }
    fclose(file);
    {
        unsigned char digest[16];
        int i;
        MD5Final(digest, &ctx);
        for (i = 0; i < 16; i++)
            sprintf(md5_out + i * 2, "%02x", digest[i]);
    }
    md5_out[32] = '\0';
    return true;
}

struct QueryResult query_md5_online_sync(const char* md5_hash) {
    char md5_upper[33];
    strncpy(md5_upper, md5_hash, 32);
    md5_upper[32] = '\0';
    ToUpper(md5_upper);

    QueryResult result;
    strcpy(result.riskLevel, "Unknown (API error)");
    result.virusName[0] = '\0';

    char url[256];
    sprintf(url, "https://www.nictasoft.com/ace/md5/%s", md5_upper);

    HINTERNET hInternet = InternetOpen("OpenRogue2025", INTERNET_OPEN_TYPE_PRECONFIG, NULL, NULL, 0);
    char responseText[8192] = "";
    char buffer[1024];
    DWORD bytesRead = 0;
    int currentLen = 0;

    if (hInternet) {
        HINTERNET hUrlFile = InternetOpenUrl(hInternet, url, NULL, 0, INTERNET_FLAG_RELOAD, 0);
        if (hUrlFile) {
            while (InternetReadFile(hUrlFile, buffer, sizeof(buffer) - 1, &bytesRead) && bytesRead != 0) {
                buffer[bytesRead] = '\0';
                if (currentLen + bytesRead < (int)sizeof(responseText)) {
                    strncat(responseText, buffer, sizeof(responseText) - currentLen - 1);
                    currentLen = (int)strlen(responseText);
                } else {
                    break;
                }
            }
            InternetCloseHandle(hUrlFile);
        }
        InternetCloseHandle(hInternet);
    }

    std::string response(responseText);
    
    if (response.find("[100% risk]") != std::string::npos) {
        strcpy(result.riskLevel, "Malware");
    } else if (response.find("[70% risk]") != std::string::npos) {
        strcpy(result.riskLevel, "Suspicious");
    } else if (response.find("[0% risk]") != std::string::npos) {
        strcpy(result.riskLevel, "Benign");
    } else if (response.find("[10% risk]") != std::string::npos) {
        strcpy(result.riskLevel, "Benign (auto verdict)");
    } else if (response.find("this file is not yet rated") != std::string::npos) {
        strcpy(result.riskLevel, "Unknown");
    } else {
        strcpy(result.riskLevel, "Unknown (Result)");
    }

    size_t detected_pos = response.find("detected as");
    if (detected_pos != std::string::npos) {
        detected_pos += 11; // Skip "detected as"
        while (detected_pos < response.length() && isspace(response[detected_pos])) {
            detected_pos++;
        }
        size_t end_pos = detected_pos;
        while (end_pos < response.length() && !isspace(response[end_pos])) {
            end_pos++;
        }
        std::string virus_name = response.substr(detected_pos, end_pos - detected_pos);
        strncpy(result.virusName, virus_name.c_str(), sizeof(result.virusName) - 1);
        result.virusName[sizeof(result.virusName) - 1] = '\0';
    } else {
        strcpy(result.virusName, "");
    }

    return result;
}

// --------------------------
// Structures for thread parameters
// --------------------------
struct ScanFileParams {
    HWND hWnd;
    char filePath[MAX_PATH];
};

struct ScanFolderParams {
    HWND hWnd;
    char folderPath[MAX_PATH];
};

// --------------------------
// Helper: Store a thread handle in the global array.
// --------------------------
void AddThreadHandle(HANDLE hThread)
{
    if (hThread) {
        EnterCriticalSection(&g_threadLock);
        if (g_ThreadHandleCount < MAX_THREADS)
            g_hThreadHandles[g_ThreadHandleCount++] = hThread;
        else
            CloseHandle(hThread);
        LeaveCriticalSection(&g_threadLock);
    }
}

// --------------------------
// Thread function: Scan a single file.
// --------------------------
DWORD WINAPI ScanFileThread(LPVOID lpParam)
{
    ScanFileParams* params = (ScanFileParams*)lpParam;
    InterlockedIncrement(&g_ActiveThreadCount);

    __try {
        char resultText[512] = "";
        struct _stat file_stat;
        if (_stat(params->filePath, &file_stat) != 0 || file_stat.st_size == 0)
            sprintf(resultText, "File: %s\nError: Empty or inaccessible file.", params->filePath);
        else {
            char md5[33];
            if (CalculateFileMD5(params->filePath, md5)) {
                QueryResult res = query_md5_online_sync(md5);
                sprintf(resultText, "File: %s | MD5: %s | Risk: %s | Virus: %s",
                        params->filePath, md5, res.riskLevel, res.virusName);
            }
            else {
                sprintf(resultText, "File: %s\nError: Could not calculate MD5.", params->filePath);
            }
        }
        // Allocate using new[] so we can pass the result to the main thread.
        char* pResult = new char[strlen(resultText) + 1];
        if (pResult)
            strcpy(pResult, resultText);

        if (g_bRunning && SafePostMessage(params->hWnd, WM_SCAN_UPDATE, 0, (LPARAM)pResult)) {
            // pResult will be freed in WM_SCAN_UPDATE.
        }
        else {
            delete [] pResult;
        }
    }
    __except(EXCEPTION_EXECUTE_HANDLER) {
        // Exception caught; optionally log error.
    }

    delete params;
    InterlockedDecrement(&g_ActiveThreadCount);
    return 0;
}

// --------------------------
// Recursively enumerate a folder and spawn a thread for each file.
// --------------------------
void EnumerateFolder(const char* folderPath, HWND hWnd)
{
    char searchPath[MAX_PATH];
    sprintf(searchPath, "%s\\*.*", folderPath);
    WIN32_FIND_DATA ffd;
    HANDLE hFind = FindFirstFile(searchPath, &ffd);
    if (hFind == INVALID_HANDLE_VALUE)
        return;
    do {
        if (strcmp(ffd.cFileName, ".") == 0 || strcmp(ffd.cFileName, "..") == 0)
            continue;
        char fullPath[MAX_PATH];
        sprintf(fullPath, "%s\\%s", folderPath, ffd.cFileName);
        if (ffd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY)
            EnumerateFolder(fullPath, hWnd);
        else {
            ScanFileParams* pParams = new ScanFileParams;
            pParams->hWnd = hWnd;
            strncpy(pParams->filePath, fullPath, MAX_PATH);
            pParams->filePath[MAX_PATH - 1] = '\0';
            HANDLE hThread = CreateThread(NULL, 0, ScanFileThread, pParams, 0, NULL);
            AddThreadHandle(hThread);
        }
    } while (FindNextFile(hFind, &ffd));
    FindClose(hFind);
}

// --------------------------
// Thread function for folder scanning.
// --------------------------
DWORD WINAPI ScanFolderThread(LPVOID lpParam)
{
    ScanFolderParams* params = (ScanFolderParams*)lpParam;
    InterlockedIncrement(&g_ActiveThreadCount);

    __try {
        EnumerateFolder(params->folderPath, params->hWnd);
        char* pFinal = new char[64];
        if (pFinal)
            strcpy(pFinal, "Folder scan enumeration complete.");
        if (g_bRunning && SafePostMessage(params->hWnd, WM_SCAN_UPDATE, 0, (LPARAM)pFinal)) {
            // pFinal will be freed in WM_SCAN_UPDATE.
        }
        else {
            delete [] pFinal;
        }
    }
    __except(EXCEPTION_EXECUTE_HANDLER) {
        // Exception caught; optionally log error.
    }

    delete params;
    InterlockedDecrement(&g_ActiveThreadCount);
    return 0;
}

// --------------------------
// Windows Application Code with OpenRogue2025 GUI Controls
// --------------------------
ATOM MyRegisterClass(HINSTANCE hInstance);
BOOL InitInstance(HINSTANCE, int);
LRESULT CALLBACK WndProc(HWND, UINT, WPARAM, LPARAM);

int WINAPI WinMain(HINSTANCE hInstance,
                   HINSTANCE hPrevInstance,
                   LPSTR lpCmdLine,
                   int nCmdShow)
{
    MSG msg;
    CoInitialize(NULL);
    hInst = hInstance;
    InitializeCriticalSection(&g_cacheLock);
    InitializeCriticalSection(&g_threadLock);

    // Instead of LoadString (which expects numeric IDs), copy our defined strings.
    _tcsncpy(szTitle, IDS_APP_TITLE, MAX_LOADSTRING);
    _tcsncpy(szWindowClass, IDC_OPENROGUE2025, MAX_LOADSTRING);

    MyRegisterClass(hInstance);
    if (!InitInstance(hInstance, nCmdShow))
    {
        DeleteCriticalSection(&g_cacheLock);
        DeleteCriticalSection(&g_threadLock);
        CoUninitialize();
        return FALSE;
    }
    // g_hWnd is set in WM_CREATE.
    while (GetMessage(&msg, NULL, 0, 0))
    {
        TranslateMessage(&msg);
        DispatchMessage(&msg);
    }
    // Wait for active threads to finish.
    while (g_ActiveThreadCount > 0)
        Sleep(50);

    // Wait for all thread handles and close them.
    EnterCriticalSection(&g_threadLock);
    if (g_ThreadHandleCount > 0)
    {
        WaitForMultipleObjects(g_ThreadHandleCount, g_hThreadHandles, TRUE, INFINITE);
        for (int i = 0; i < g_ThreadHandleCount; i++)
            CloseHandle(g_hThreadHandles[i]);
        g_ThreadHandleCount = 0;
    }
    LeaveCriticalSection(&g_threadLock);

    DeleteCriticalSection(&g_cacheLock);
    DeleteCriticalSection(&g_threadLock);
    CoUninitialize();
    return (int)msg.wParam;
}

ATOM MyRegisterClass(HINSTANCE hInstance)
{
    WNDCLASSEX wcex;
    wcex.cbSize         = sizeof(WNDCLASSEX);
    wcex.style          = CS_HREDRAW | CS_VREDRAW;
    wcex.lpfnWndProc    = WndProc;
    wcex.cbClsExtra     = 0;
    wcex.cbWndExtra     = 0;
    wcex.hInstance      = hInstance;
    wcex.hIcon          = LoadIcon(hInstance, MAKEINTRESOURCE(IDI_OPENROGUE2025));
    wcex.hCursor        = LoadCursor(NULL, IDC_ARROW);
    wcex.hbrBackground  = (HBRUSH)(COLOR_WINDOW+1);
    wcex.lpszMenuName   = NULL;
    wcex.lpszClassName  = szWindowClass;
    wcex.hIconSm        = LoadIcon(hInstance, MAKEINTRESOURCE(IDI_SMALL));
    return RegisterClassEx(&wcex);
}

BOOL InitInstance(HINSTANCE hInstance, int nCmdShow)
{
    HWND hWnd = CreateWindow(szWindowClass, szTitle, WS_OVERLAPPEDWINDOW,
                             CW_USEDEFAULT, 0, 800, 600, NULL, NULL, hInstance, NULL);
    if (!hWnd)
        return FALSE;
    ShowWindow(hWnd, nCmdShow);
    UpdateWindow(hWnd);
    return TRUE;
}

LRESULT CALLBACK WndProc(HWND hWnd, UINT message, WPARAM wParam, LPARAM lParam)
{
    static HFONT hBannerFont = NULL;
    int wmId;
    switch (message)
    {
    case WM_CREATE:
        {
            g_hWnd = hWnd;
            HWND hBanner = CreateWindow("STATIC", "OpenRogue2025 - Rogue",
                WS_CHILD | WS_VISIBLE | SS_CENTER,
                10, 10, 760, 40, hWnd, (HMENU)IDC_STATIC_BANNER, hInst, NULL);
            CreateWindow("STATIC", "Selected File:",
                WS_CHILD | WS_VISIBLE,
                10, 60, 100, 20, hWnd, (HMENU)IDC_STATIC_FILE, hInst, NULL);
            hEditFile = CreateWindow("EDIT", "",
                WS_CHILD | WS_VISIBLE | WS_BORDER | ES_AUTOHSCROLL,
                120, 60, 500, 20, hWnd, (HMENU)IDC_EDIT_FILE, hInst, NULL);
            CreateWindow("BUTTON", "Browse",
                WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON,
                630, 60, 100, 20, hWnd, (HMENU)IDC_BUTTON_BROWSE, hInst, NULL);
            CreateWindow("BUTTON", "Scan File",
                WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON,
                10, 90, 100, 30, hWnd, (HMENU)IDC_BUTTON_SCAN, hInst, NULL);
            CreateWindow("STATIC", "Selected Directory:",
                WS_CHILD | WS_VISIBLE,
                10, 140, 150, 20, hWnd, (HMENU)IDC_STATIC_FOLDER, hInst, NULL);
            hEditFolder = CreateWindow("EDIT", "",
                WS_CHILD | WS_VISIBLE | WS_BORDER | ES_AUTOHSCROLL,
                170, 140, 450, 20, hWnd, (HMENU)IDC_EDIT_FOLDER, hInst, NULL);
            CreateWindow("BUTTON", "Browse Folder",
                WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON,
                630, 140, 100, 20, hWnd, (HMENU)IDC_BUTTON_FOLDER_BROWSE, hInst, NULL);
            CreateWindow("BUTTON", "Scan Folder",
                WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON,
                10, 170, 100, 30, hWnd, (HMENU)IDC_BUTTON_FOLDER_SCAN, hInst, NULL);
            // New Remove Malware button placed to the right of "Scan Folder"
            CreateWindow("BUTTON", "Remove Malware",
                WS_CHILD | WS_VISIBLE | BS_PUSHBUTTON,
                120, 170, 140, 30, hWnd, (HMENU)IDC_BUTTON_REMOVE, hInst, NULL);

            // Create a list box for displaying scan results with horizontal scrolling enabled.
            hListResult = CreateWindow("LISTBOX", "",
                WS_CHILD | WS_VISIBLE | WS_BORDER | LBS_NOTIFY | WS_VSCROLL | WS_HSCROLL,
                10, 220, 760, 330, hWnd, (HMENU)IDC_LIST_RESULT, hInst, NULL);

            hBannerFont = CreateFont(24, 0, 0, 0, FW_BOLD, FALSE, FALSE, FALSE,
                                      DEFAULT_CHARSET, OUT_DEFAULT_PRECIS, CLIP_DEFAULT_PRECIS,
                                      DEFAULT_QUALITY, DEFAULT_PITCH, "Arial");
            SendMessage(hBanner, WM_SETFONT, (WPARAM)hBannerFont, TRUE);
        }
        break;
    case WM_COMMAND:
        wmId = LOWORD(wParam);
        switch (wmId)
        {
        case IDC_BUTTON_BROWSE:
            {
                char filename[MAX_PATH] = "";
                OPENFILENAME ofn;
                ZeroMemory(&ofn, sizeof(ofn));
                ofn.lStructSize = sizeof(ofn);
                ofn.hwndOwner = hWnd;
                ofn.lpstrFilter = "All Files\0*.*\0";
                ofn.lpstrFile = filename;
                ofn.nMaxFile = sizeof(filename);
                ofn.lpstrTitle = "Select a file to scan";
                if (GetOpenFileName(&ofn))
                {
                    SetWindowText(hEditFile, filename);
                    // Reset the list box and add initial message.
                    SendMessage(hListResult, LB_RESETCONTENT, 0, 0);
                    SendMessage(hListResult, LB_ADDSTRING, 0, (LPARAM)"Scan result will appear here.");
                }
            }
            break;
        case IDC_BUTTON_SCAN:
            {
                char filename[MAX_PATH] = "";
                GetWindowText(hEditFile, filename, MAX_LOADSTRING);
                if (strlen(filename) == 0)
                {
                    MessageBox(hWnd, "Please select a file first.", "Scan Error", MB_OK);
                    break;
                }
                {
                    ScanFileParams* pParams = new ScanFileParams;
                    pParams->hWnd = hWnd;
                    strncpy(pParams->filePath, filename, MAX_PATH);
                    pParams->filePath[MAX_PATH - 1] = '\0';
                    HANDLE hThread = CreateThread(NULL, 0, ScanFileThread, pParams, 0, NULL);
                    AddThreadHandle(hThread);
                }
                // Reset list box and show start message.
                SendMessage(hListResult, LB_RESETCONTENT, 0, 0);
                SendMessage(hListResult, LB_ADDSTRING, 0, (LPARAM)"File scan started...");
            }
            break;
        case IDC_BUTTON_FOLDER_BROWSE:
            {
                BROWSEINFO bi = {0};
                bi.hwndOwner = hWnd;
                bi.lpszTitle = "Select a folder to scan";
                LPITEMIDLIST pidl = SHBrowseForFolder(&bi);
                if (pidl != NULL)
                {
                    char folderPath[MAX_PATH];
                    if (SHGetPathFromIDList(pidl, folderPath))
                    {
                        SetWindowText(hEditFolder, folderPath);
                        SendMessage(hListResult, LB_RESETCONTENT, 0, 0);
                        SendMessage(hListResult, LB_ADDSTRING, 0, (LPARAM)"Scan result will appear here.");
                    }
                    CoTaskMemFree(pidl);
                }
            }
            break;
        case IDC_BUTTON_FOLDER_SCAN:
            {
                char folderPath[MAX_PATH] = "";
                GetWindowText(hEditFolder, folderPath, MAX_LOADSTRING);
                if (strlen(folderPath) == 0)
                {
                    MessageBox(hWnd, "Please select a folder first.", "Scan Error", MB_OK);
                    break;
                }
                {
                    ScanFolderParams* pParams = new ScanFolderParams;
                    pParams->hWnd = hWnd;
                    strncpy(pParams->folderPath, folderPath, MAX_PATH);
                    pParams->folderPath[MAX_PATH - 1] = '\0';
                    HANDLE hThread = CreateThread(NULL, 0, ScanFolderThread, pParams, 0, NULL);
                    AddThreadHandle(hThread);
                }
                SendMessage(hListResult, LB_RESETCONTENT, 0, 0);
                SendMessage(hListResult, LB_ADDSTRING, 0, (LPARAM)"Folder scan started...");
            }
            break;
        case IDC_BUTTON_REMOVE:
            {
                // This is a demo. In the full product, malware removal is supported.
                MessageBox(hWnd, 
                    "This is a demo version.\n\nFor malware removal and full product features, please contact:\nprotonkral5668@proton.me", 
                    "Full Product Available", 
                    MB_OK | MB_ICONINFORMATION);
            }
            break;
        case IDM_COPY:
            {
                // Copy the currently selected item from the list box.
                int sel = SendMessage(hListResult, LB_GETCURSEL, 0, 0);
                if (sel != LB_ERR) {
                    int len = SendMessage(hListResult, LB_GETTEXTLEN, sel, 0);
                    char* buffer = (char*)malloc(len + 1);
                    if (buffer) {
                        SendMessage(hListResult, LB_GETTEXT, sel, (LPARAM)buffer);
                        if (OpenClipboard(hWnd)) {
                            EmptyClipboard();
                            HGLOBAL hGlob = GlobalAlloc(GMEM_MOVEABLE, len + 1);
                            if (hGlob) {
                                char* pData = (char*)GlobalLock(hGlob);
                                if (pData) {
                                    strcpy(pData, buffer);
                                    GlobalUnlock(hGlob);
                                    SetClipboardData(CF_TEXT, hGlob);
                                }
                            }
                            CloseClipboard();
                        }
                        free(buffer);
                    }
                }
            }
            break;
        default:
            return DefWindowProc(hWnd, message, wParam, lParam);
        }
        break;
    case WM_CONTEXTMENU:
        {
            // If the context menu was requested in the listbox, show a copy command.
            if ((HWND)wParam == hListResult) {
                POINT pt;
                pt.x = LOWORD(lParam);
                pt.y = HIWORD(lParam);
                if (pt.x == -1 && pt.y == -1) {
                    GetCursorPos(&pt);
                }
                HMENU hMenu = CreatePopupMenu();
                if (hMenu) {
                    AppendMenu(hMenu, MF_STRING, IDM_COPY, "Copy");
                    TrackPopupMenu(hMenu, TPM_LEFTALIGN | TPM_RIGHTBUTTON, pt.x, pt.y, 0, hWnd, NULL);
                    DestroyMenu(hMenu);
                }
            }
        }
        break;
    case WM_SCAN_UPDATE:
        {
            // pUpdateText was allocated with new[]; free it with delete[] after use.
            char* pUpdateText = (char*)lParam;
            if (pUpdateText)
            {
                if (hListResult && IsWindow(hListResult))
                {
                    // Add the scan result as a new item in the list box.
                    SendMessage(hListResult, LB_ADDSTRING, 0, (LPARAM)pUpdateText);

                    // Update horizontal extent based on text width.
                    HDC hdc = GetDC(hListResult);
                    SIZE size;
                    GetTextExtentPoint32(hdc, pUpdateText, strlen(pUpdateText), &size);
                    ReleaseDC(hListResult, hdc);
                    int currentExtent = SendMessage(hListResult, LB_GETHORIZONTALEXTENT, 0, 0);
                    if (size.cx > currentExtent) {
                        SendMessage(hListResult, LB_SETHORIZONTALEXTENT, size.cx, 0);
                    }
                }
                delete [] pUpdateText;
            }
        }
        break;
    case WM_DESTROY:
        g_bRunning = FALSE;
        while (g_ActiveThreadCount > 0)
            Sleep(50);
        EnterCriticalSection(&g_threadLock);
        if (g_ThreadHandleCount > 0)
        {
            WaitForMultipleObjects(g_ThreadHandleCount, g_hThreadHandles, TRUE, INFINITE);
            for (int i = 0; i < g_ThreadHandleCount; i++)
                CloseHandle(g_hThreadHandles[i]);
            g_ThreadHandleCount = 0;
        }
        LeaveCriticalSection(&g_threadLock);
        if (hBannerFont)
            DeleteObject(hBannerFont);
        PostQuitMessage(0);
        break;
    default:
        return DefWindowProc(hWnd, message, wParam, lParam);
    }
    return 0;
}

