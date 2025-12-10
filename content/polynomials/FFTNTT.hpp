/**
 * Author: Some Chinese guy in codeforces
 * Date: 2025-01-11
 * Description: basic operations of formal power series
 */

using ll = long long;
using poly = vector<ll>;
const ll M=998244353; // M=7340033 -> pr=5, M=998244353 -> pr=3
ll pr=3,inv_pr,m;

int qp(int a, int e = M - 2) {
    ll r = 1, x = a % M;
    while (e > 0) {if (e & 1) r = r * x % M;x = x * x % M;e >>= 1;}
    return (int)r;
}

void ntt(poly &a, bool inv) {
    int n = a.size();
    static poly rev, roots{0,1};
    if ((int)rev.size() != n) {
        int L = __builtin_ctz(n);
        rev.assign(n,0);
        for (int i = 0; i < n; i++) rev[i] = (rev[i>>1]>>1) | ((i&1)<<(L-1));
    }
    for (int i = 0; i < n; i++) if (i<rev[i]) swap(a[i], a[rev[i]]);
 
    if ((int)roots.size() < n) {
        int k = __builtin_ctz(roots.size());
        roots.resize(n);
        while ((1<<k) < n) {
            int e = qp(pr, (M-1) >> (k+1));
            for (int i = 1<<(k-1); i < (1<<k); i++) {
                roots[2*i]   = roots[i];
                roots[2*i+1] = (ll)roots[i] * e % M;
            }
            k++;
        }
    }
 
    for (int len = 1; len < n; len <<= 1) {
        for (int i = 0; i < n; i += 2*len) {
            for (int j = 0; j < len; j++) {
                int u = a[i+j];
                int v = (ll)a[i+j+len] * roots[len+j] % M;
                a[i+j]       = u + v < M ? u + v : u + v - M;
                a[i+j+len]   = u - v >= 0 ? u - v : u - v + M;
            }
        }
    }
 
    if (inv) {
        reverse(a.begin()+1, a.end());
        int inv_n = qp(n);
        for (auto &x : a) x = (ll)x * inv_n % M;
    }
}

using cd = complex<double>; //a + bi (real,imag)
const double PI = acos(-1);

void fft(vector<cd> & a, bool invert) {
    int n = a.size();

    for (int i = 1, j = 0; i < n; i++) {
        int bit = n >> 1;
        for (; j & bit; bit >>= 1)
            j ^= bit;
        j ^= bit;

        if (i < j)
            swap(a[i], a[j]);
    }

    for (int len = 2; len <= n; len <<= 1) {
        double ang = 2 * PI / len * (invert ? -1 : 1);
        cd wlen(cos(ang), sin(ang));
        for (int i = 0; i < n; i += len) {
            cd w(1);
            for (int j = 0; j < len / 2; j++) {
                cd u = a[i+j], v = a[i+j+len/2] * w;
                a[i+j] = u + v;
                a[i+j+len/2] = u - v;
                w *= wlen;
            }
        }
    }

    if (invert) {
        for (cd & x : a)
            x /= n;
    }
}

poly multiply(poly a, poly b) {
    int sz = a.size() + b.size() - 1;
    int n = 1; while (n < sz) n <<= 1;
    a.resize(n); b.resize(n);
    ntt(a, false); ntt(b, false);
    for (int i = 0; i < n; i++) a[i] = (ll)a[i] * b[i] % M;
    ntt(a, true);
    a.resize(sz);
    return a;
}

vector<cd> multiply(vector<cd> a, vector<cd> b) {
    int sz = a.size() + b.size() - 1;
    int n = 1; while (n < sz) n <<= 1;
    a.resize(n); b.resize(n);
    fft(a, false); fft(b, false);
    for (int i = 0; i < n; i++) a[i] = a[i] * b[i];
    fft(a, true);
    a.resize(sz);
    return a;
}

poly poly_inv(poly f, int m) {
    poly g(1, qp(f[0])); // g0 = 1/f0
    for (int len = 1; len < m; len <<= 1) {
        poly f_cut(f.begin(), f.begin() + min((int)f.size(), 2*len));
        auto tmp = multiply(multiply(g, g), f_cut);
        tmp.resize(2*len);       
        g.resize(2*len);
        for (int i = 0; i < 2*len; i++) {
            g[i] = ((2LL*g[i] - tmp[i]) % M + M) % M;
        }
    }
    g.resize(m);
    return g;
}
 
// f[0]=1 needed
poly poly_sqrt(const poly& f, int m) {
    poly g(1,1);
    int inv2 = (M + 1) / 2;
    for (int len = 1; len < m; len <<= 1) {
        auto g2 = multiply(g, g);
        poly sum(2*len);
        for (int i = 0; i < 2*len; i++) {
            int v = (i < (int)f.size() ? f[i] : 0);
            sum[i] = (v + (i < (int)g2.size() ? g2[i] : 0)) % M;
        }
        auto inv_g = poly_inv(g, 2*len);
        g = multiply(sum, inv_g);
        for (auto &x : g) x = (ll)x * inv2 % M;
        g.resize(2*len);
    }
    g.resize(m);
    return g;
}
 
// derivative
poly poly_d(const poly& f) {
    int n = f.size();
    poly g(max<int>(0,n-1));
    for (int i = 1; i < n; i++) g[i-1] = (ll)f[i]*i % M;
    return g;
}
 
// integral
poly poly_int(const poly& f) {
    int n = f.size();
    poly g(n+1);
    
    static poly inv{0,1};
    {    
        while ((int)inv.size() <= n) {
            int i = inv.size();
            inv.push_back((ll)(M - M/i) * inv[M % i] % M);
        }
    }
    
    for (int i = 0; i < n; i++) g[i+1] = (ll)f[i] * inv[i+1] % M;
    return g;
}
 
// ln(f)，f[0]=1
poly poly_ln(const poly& f, int m) {
    auto df = poly_d(f);
    auto invf = poly_inv(f, m);
    auto q = multiply(df, invf);
    q.resize(m-1);
    auto res = poly_int(q);
    res.resize(m);
    return res;
}
 
// exp(f), f[0]=0 
poly poly_exp(const poly& f, int m) {
    poly g(1,1);
    for (int len = 1; len < m; len <<= 1) {
        auto g_ln = poly_ln(g, 2*len);
        poly diff(2*len);
        for (int i = 0; i < 2*len; i++) {
            diff[i] = ((i < (int)f.size() ? f[i] : 0) - g_ln[i] + M) % M;
        }
        diff[0] = (diff[0] + 1) % M;
        g = multiply(g, diff);
        g.resize(2*len);
    }
    g.resize(m);
    return g;
}
 
// f^k，f[0]=1 or constant term is 0 ，O(m log m)
poly poly_pow(const poly& f, ll k, int m) {
    auto ln_f = poly_ln(f, m);
    for (int i = 0; i < m; i++) ln_f[i] = (ll)ln_f[i] * (k % (M-1)) % M;
    return poly_exp(ln_f, m);
}
 
// a = b*q + r : cal(q,r)
pair<poly, poly> poly_divmod(poly a, poly b) {
    int n = a.size(), m = b.size();
    if (n < m) return {{0}, a};
    poly ra(a.rbegin(), a.rend()), rb(b.rbegin(), b.rend());
    int k = n-m+1;
    auto inv_rb = poly_inv(rb, k);
    auto rq = multiply(ra, inv_rb);
    rq.resize(k);
    poly q(rq.rbegin(), rq.rend());
    // remainder r = a - b*q
    auto bq = multiply(b, q);
    poly r = a;
    for (int i = 0; i < (int)bq.size(); i++)
        r[i] = (r[i] - bq[i] + M) % M;
    r.resize(m-1);
    return {q, r};
}

int main (){
    ios::sync_with_stdio(0); cin.tie(0);
    vector<cd> a={1,2}, b={3,4};
    vector<cd> c=multiply(a,b);
    for (auto e:c) cout << e << ' ';
}