#include <iostream>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <cmath>
#include <algorithm>
#include <queue>
#include <map>
#include <set>
#include <vector>
#include <string>
#include <stack>
#include <bitset>
#include <ctime>
#include <windows.h>
#define INF 0x3f3f3f3f
#define eps 1e-8
#define FI first
#define SE second

using namespace std;

typedef long long ll;

const int MaxN = 15000;

const int MaxM = 1200000;

const int Maxn = 1100;

int N, M, K;

pair <int, int> E[MaxM];

void read() {
    scanf("%d%d%d", &N, &M, &K);
    for(int i = 0; i < M; ++ i) {
        scanf("%d%d", &E[i].FI, &E[i].SE);
        -- E[i].FI; -- E[i].SE;
    }
}

int DEG[MaxN], head[MaxN], nxt[MaxM], to[MaxM], ecnt;

int que[MaxN], nV[MaxN];

bool outcore[MaxN];

int degree[Maxn], dominate[Maxn], n;

bitset <Maxn> Graph[Maxn];

void addedge(int *h, int v) {
    nxt[ecnt] = *h;
    to[ecnt] = v;
    *h = ecnt ++;
}

inline bool checkdominate(int u, int v) {
    if(Graph[u] == Graph[v]) return u > v;
    bitset <Maxn> tmp = Graph[u];
    tmp.set(u);
    tmp &= Graph[v];
    return tmp == Graph[v];
}

bool del[Maxn], ins[Maxn];

int notadj[Maxn];

vector <int> delvex, svex;

int LB;

bool PreProcess(int S) {
    memset(DEG, 0, N * sizeof(int));
    memset(head, -1, N * sizeof(int));
    ecnt = 0;
    for(int i = 0; i < M; ++ i) {
        ++ DEG[E[i].FI];
        ++ DEG[E[i].SE];
        addedge(head + E[i].FI, E[i].SE);
        addedge(head + E[i].SE, E[i].FI);
    }
    memset(outcore, 0, N * sizeof(bool));
    int fr = 0, re = 0;
    for(int i = 0; i < N; ++ i) {
        if(DEG[i] < S - K) {
            que[re ++] = i;
            outcore[i] = true;
        }
    }
    while(fr ^ re) {
        int u = que[fr ++];
        for(int e = head[u]; ~e; e = nxt[e]) {
            int v = to[e];
            if(outcore[v]) continue;
            if(-- DEG[v] < S - K) {
                que[re ++] = v;
                outcore[v] = true;
            }
        }
    }
    n = 0;
    for(int i = 0; i < N; ++ i) {
        if(!outcore[i])
            nV[i] = n ++;
    }
    if(n < S) return false;
    for(int i = 0; i < n; ++ i) Graph[i].reset();
    memset(head, -1, n * sizeof(int));
    memset(dominate, -1, n * sizeof(int));
    memset(degree, 0, n * sizeof(int));
    ecnt = 0;
    for(int i = 0; i < M; ++ i) {
        int u = E[i].FI, v = E[i].SE;
        if(outcore[u] || outcore[v]) continue;
        u = nV[u]; v = nV[v];
        ++ degree[u]; ++ degree[v];
        addedge(head + u, v);
        addedge(head + v, u);
        Graph[u].set(v);
        Graph[v].set(u);
    }
    for(int i = 0; i < n; ++ i) {
        for(int j = i + 1; j < n; ++ j) {
            if(checkdominate(i, j))
                addedge(dominate + i, j);
            if(checkdominate(j, i))
                addedge(dominate + j, i);
        }
    }
    delvex.clear(); svex.clear();
    memset(ins, 0, n * sizeof(bool));
    memset(del, 0, n * sizeof(bool));
    memset(notadj, 0, n * sizeof(int));
    LB = S - 1;
    return true;
}

inline void delfrD(int u) {
    del[u] = true;
    delvex.push_back(u);
    for(int e = head[u]; ~e; e = nxt[e]) -- degree[to[e]];
}

inline void addtoD(int u) {
    del[u] = false;
    delvex.pop_back();
    for(int e = head[u]; ~e; e = nxt[e]) ++ degree[to[e]];
}

inline void delfrS(int u) {
    ins[u] = false;
    svex.pop_back();
    for(int i = 0; i < n; ++ i) {
        if(i != u && !Graph[u].test(i))
            -- notadj[i];
    }
}

inline void addtoS(int u) {
    ins[u] = true;
    svex.push_back(u);
    for(int i = 0; i < n; ++ i) {
        if(i != u && !Graph[u].test(i))
            ++ notadj[i];
    }
}

inline bool canadd(int u) {
    int tot = 0;
    for(auto v : svex) if(!Graph[u].test(v)) {
        if(++ tot >= K) return false;
        if(notadj[v] >= K - 1) return false;
    }
    return true;
}

int dis[Maxn];

void bfs(int s) {
    memset(dis, -1, n * sizeof(int));
    dis[s] = 0;
    int fr = 0, re = 0;
    que[re ++] = s;
    while(fr ^ re) {
        int u = que[fr ++];
        for(int e = head[u]; ~e; e = nxt[e]) {
            int v = to[e];
            if(del[v] || dis[v] != -1) continue;
            dis[v] = dis[u] + 1;
            que[re ++] = v;
        }
    }
}

/*bool select(vector <int> &vex, int p, int curS, int last) {
    if(curS <= LB) return false;
    int minID = -1;
    for(int i = 0; i < n; ++ i) if(!del[i]) {
        if(minID == -1 || degree[i] < degree[minID])
            minID = i;
    }
    if(degree[minID] >= curS - K) return true;
    if(degree[minID] < LB + 1 - K) {
        if(ins[minID]) return false;
        delfrD(minID);
        bool ret = select(vex, p, curS - 1, last);
        addtoD(minID);
        return ret;
    }
    int maxID = -1;
    for(int i = 0; i < n; ++ i) if(!del[i]) {
        if(maxID == -1 || notadj[i] > notadj[maxID])
            maxID = i;
    }
    if(!ins[maxID] && notadj[maxID] >= K) {
        delfrD(maxID);
        bool ret = select(vex, p, curS - 1, last);
        addtoD(maxID);
        return ret;
    }
    if(ins[maxID] && notadj[maxID] >= K - 1) {
        if(notadj[maxID] >= K) return false;
        vector <int> todel;
        for(int i = 0; i < n; ++ i) if(!del[i] && !ins[i] && !Graph[maxID].test(i)) {
            todel.push_back(i);
        }
        if(todel.size()) {
            for(auto x : todel) delfrD(x);
            bool ret = select(vex, p, curS - todel.size(), last);
            for(auto x : todel) addtoD(x);
            return ret;
        }
    }
    set <int> sofar;
    for(auto u : delvex) {
        for(int e = dominate[u]; ~e; e = nxt[e]) {
            int v = to[e];
            if(del[v]) continue;
            if(ins[v]) return false;
            sofar.insert(v);
        }
    }
    if(sofar.size()) {
        for(auto x : sofar) delfrD(x);
        bool ret = select(vex, p, curS - sofar.size(), last);
        for(auto x : sofar) addtoD(x);
        return ret;
    }
    for(auto u : svex) {
        bfs(u);
        for(int v = 0; v < n; ++ v) if(!del[v]) {
            if(dis[v] == -1 || dis[v] > max(2, K + K - LB)) {
                if(ins[v]) return false;
                sofar.insert(v);
            }
        }
    }
    if(sofar.size()) {
        for(auto x : sofar) delfrD(x);
        bool ret = select(vex, p, curS - sofar.size(), last);
        for(auto x : sofar) addtoD(x);
        return ret;
    }
    if(p == (int)vex.size()) return dfs(curS);
    int v = vex[p];
    if(del[v]) return select(vex, p + 1, curS, last);
    delfrD(v);
    bool ret = select(vex, p + 1, curS - 1, last);
    addtoD(v);
    if(ret) return true;
    if(last && canadd(v)) {
        addtoS(v);
        ret = select(vex, p + 1, curS, last - 1);
        delfrS(v);
        if(ret) return true;
    }
    return false;
}*/

LARGE_INTEGER t1, t2, tc;

bool dfs(int curS) {
    if(curS <= LB) return false;
    int minID = -1;
    for(int i = 0; i < n; ++ i) if(!del[i]) {
        if(minID == -1 || degree[i] < degree[minID])
            minID = i;
    }
    if(degree[minID] >= curS - K) return true;
    if(degree[minID] < LB + 1 - K) {
        if(ins[minID]) return false;
        delfrD(minID);
        bool ret = dfs(curS - 1);
        addtoD(minID);
        return ret;
    }
    int maxID = -1;
    for(int i = 0; i < n; ++ i) if(!del[i]) {
        if(maxID == -1 || notadj[i] > notadj[maxID])
            maxID = i;
    }
    if(!ins[maxID] && notadj[maxID] >= K) {
        delfrD(maxID);
        bool ret = dfs(curS - 1);
        addtoD(maxID);
        return ret;
    }
    if(ins[maxID] && notadj[maxID] >= K - 1) {
        if(notadj[maxID] >= K) return false;
        vector <int> todel;
        for(int i = 0; i < n; ++ i) if(!del[i] && !ins[i] && !Graph[maxID].test(i)) {
            todel.push_back(i);
        }
        if(todel.size()) {
            for(auto x : todel) delfrD(x);
            bool ret = dfs(curS - todel.size());
            for(auto x : todel) addtoD(x);
            return ret;
        }
    }
    set <int> sofar;
    for(auto u : delvex) {
        for(int e = dominate[u]; ~e; e = nxt[e]) {
            int v = to[e];
            if(del[v]) continue;
            if(ins[v]) return false;
            sofar.insert(v);
        }
    }
    if(sofar.size()) {
        for(auto x : sofar) delfrD(x);
        bool ret = dfs(curS - sofar.size());
        for(auto x : sofar) addtoD(x);
        return ret;
    }
    for(auto u : svex) {
        bfs(u);
        for(int v = 0; v < n; ++ v) if(!del[v]) {
            if(dis[v] == -1 || dis[v] > max(2, K + K - LB)) {
                if(ins[v]) return false;
                sofar.insert(v);
            }
        }
    }
    if(sofar.size()) {
        for(auto x : sofar) delfrD(x);
        bool ret = dfs(curS - sofar.size());
        for(auto x : sofar) addtoD(x);
        return ret;
    }
    vector <int> branch;
    for(int x = 0; x < n; ++ x) if(!del[x] && x != minID && !ins[x]) {
        if(!Graph[minID].test(x))
            branch.push_back(x);
    }
    random_shuffle(branch.begin(), branch.end());
    if(ins[minID]) {
        int canselect = K - 1 - notadj[minID], pos = -1;
        bool ret = false;
        for(int i = 0; !ret && i < canselect; ++ i) {
            delfrD(branch[i]);
            if(i && !canadd(branch[i - 1])) {
                addtoD(branch[i]);
                break;
            }
            if(i) {
                addtoS(branch[i - 1]);
                pos = i - 1;
            }
            ret |= dfs(curS - 1);
            addtoD(branch[i]);
        }
        if(ret) {
            for(int i = 0; i <= pos; ++ i) delfrS(branch[i]);
            return true;
        }
        for(int i = canselect; i < (int)branch.size(); ++ i) {
            delfrD(branch[i]);
        }
        if(canselect == 0 || canadd(branch[canselect - 1])) {
            if(canselect) addtoS(branch[canselect - 1]);
            ret |= dfs(curS - branch.size() + canselect);
            if(canselect) delfrS(branch[canselect - 1]);
        }
        for(int i = 0; i <= pos; ++ i) delfrS(branch[i]);
        for(int i = canselect; i < (int)branch.size(); ++ i) {
            addtoD(branch[i]);
        }
        return ret;
    } else {
        delfrD(minID);
        bool ret = dfs(curS - 1);
        addtoD(minID);
        if(ret) return true;
        int canselect = K - 1 - notadj[minID];
        if(!canadd(minID)) return false;
        addtoS(minID);
        int pos = -1;
        for(int i = 0; !ret && i < canselect; ++ i) {
            delfrD(branch[i]);
            if(i && !canadd(branch[i - 1])) {
                addtoD(branch[i]);
                break;
            }
            if(i) {
                addtoS(branch[i - 1]);
                pos = i - 1;
            }
            ret |= dfs(curS - 1);
            addtoD(branch[i]);
        }
        if(ret) {
            for(int i = 0; i <= pos; ++ i) delfrS(branch[i]);
            delfrS(minID);
            return true;
        }
        for(int i = canselect; i < (int)branch.size(); ++ i) {
            delfrD(branch[i]);
        }
        if(canselect == 0 || canadd(branch[canselect - 1])) {
            if(canselect) addtoS(branch[canselect - 1]);
            ret |= dfs(curS - branch.size() + canselect);
            if(canselect) delfrS(branch[canselect - 1]);
        }
        for(int i = 0; i <= pos; ++ i) delfrS(branch[i]);
        for(int i = canselect; i < (int)branch.size(); ++ i) {
            addtoD(branch[i]);
        }
        delfrS(minID);
        return ret;
    }
}

void work() {
    int l = K + 1, r = N;
    int ansL = min(N, K), ansR = N;
    while(l <= r) {
        int m = (l + r) >> 1;
        if(!PreProcess(m)) {
            ansR = r = m - 1;
            continue;
        }
        if(dfs(n)) {
            ansL = m;
            l = m + 1;
        } else {
            ansR = r = m - 1;
        }
    }
    printf("%d %d\n", ansL, ansR);
}

char infile[100], outfile[100];

void MAIN() {
    freopen(infile, "r", stdin);
    freopen(outfile, "w", stdout);
    srand(time(NULL));
    read();
    QueryPerformanceFrequency(&tc);
    QueryPerformanceCounter(&t1);
    work();
    QueryPerformanceCounter(&t2);
    printf("Use Time: %.10f\n", (t2.QuadPart - t1.QuadPart) * 1.0 / tc.QuadPart);
}

int main() {
    MAIN();
    return 0;
}
