/*
Certificate for W_r[Psi_1] of the Riemann theta kernel, r=1,...,5.
Let y=pi exp(4t), x=1/sqrt(y), p=n^2, F(y)=Psi_1(t).
Substitution z=p*pi*exp(4v) in the integral and integration by parts give
 F(y) = (pi^(-1/4)/2)*y^(5/4) sum_p p [
 exp(-p*y) - (1/4) integral_1^infty v^(1/4) exp(-p*y*v) dv ].
The index runs over positive squares. At each fixed y form the two-variable
kernel F(y*(1+x*u)*(1+x*v)). Multiply by the positive constant
2*pi^(1/4)*exp(y)/y^(5/4), and in each variable by
exp(u/x)/(1+x*u)^(5/4). These substitutions act on the Taylor coefficient
matrices by left/right triangular matrices with positive diagonal:
t is shifted by log(1+x*u)/4 and log(1+x*v)/4. All leading signs are preserved.
After changing the integration variable to w=p*y*(v_old-1), the resulting
kernel is a sum of p*exp(-(p-1)*y) times
 K(0) - x^2/(4*p) integral_0^infty exp(-w)*(1+w*x^2/p)^(1/4)*K(w) dw,
 K(w)=exp(-d_w*(u+v)-q_w*u*v),
 d_w=(p-1)/x+w*x, q_w=p+w*x^2.
Coefficient extraction gives exactly the polynomials in check().
The first square has a regular limit at x=0. Larger squares are bounded
uniformly there. The compact range tested contains [0,1/sqrt(pi)].

Tail bound for one square and any coefficient i,j<=4:
the absolute coefficient of K(w) is at most 5*(1+q_w)^4*(1+d_w)^8,
hence at most 5*(2*p)^12*y^4*(1+w)^12 when y>=3. The fourth
root in the integral is at most 1+w. Using integral exp(-w)*(1+w)^13
dw < e*13! gives the bound 5*2^12*3e10*n^26*y^4*exp(-(n^2-1)*y)
including both terms. In the omitted ranges this decreases in y,
and the consecutive-n ratio is at most (3/2)^26*exp(-15)<1/2.
The sum is bounded by twice its first majorant. verify_tail() checks this
at (n,y)=(12,3),(2,64). The finite quadrature uses monotone weights and
exact incomplete exponential moments with outward interval rounding.
*/
// g++ -O2 -std=c++17 -fno-fast-math -ffp-contract=off certyfikat_theta_W5.cpp -o w5 && ./w5
// IEEE binary64, correctly rounded +,-,*,/,sqrt; interval endpoints outward.
#include <cmath>
#include <algorithm>
#include <iostream>
#include <stdexcept>
#include <limits>
using namespace std;
static_assert(numeric_limits<double>::is_iec559 && numeric_limits<double>::digits==53);
struct I {double l,h; I(double a=0):l(a),h(a){} I(double a,double b):l(a),h(b){}};
double lo(double a){return nextafter(a,-INFINITY);} double hi(double a){return nextafter(a,INFINITY);}
I operator+(I a,I b){return {lo(a.l+b.l),hi(a.h+b.h)};}
I operator-(I a,I b){return {lo(a.l-b.h),hi(a.h-b.l)};}
I operator*(I a,I b){double A=a.l*b.l,B=a.l*b.h,C=a.h*b.l,D=a.h*b.h;return {lo(min({A,B,C,D})),hi(max({A,B,C,D}))};}
I operator/(I a,I b){if(b.l<=0 && b.h>=0)throw runtime_error("division");return a*I(lo(1/b.h),hi(1/b.l));}
I root(I a){return {lo(sqrt(a.l)),hi(sqrt(a.h))};}
I expminus_point(double a){
 if(a>=700)return {0,ldexp(1.,-990)};
 int k=0; while(a>0.25){a*=0.5;++k;}
 I s=1,term=1;
 for(int j=1;j<=17;j++){term=term*I(-a)/I(j);s=s+term;}
 I upper=s-term; I r(s.l,upper.h);
 while(k-->0)r=r*r;
 return r;
}
I expminus(I a){return {expminus_point(a.h).l,expminus_point(a.l).h};}
constexpr int bins=256; // bins of width 1/4 in the integration variable
I mass[bins][10],tail[10]; double fact[11];
void init(){
 fact[0]=1;for(int j=1;j<=10;j++)fact[j]=j*fact[j-1];
 I prev[10];
 for(int b=0;b<=bins;b++){
  double w=b*.25; I e=expminus_point(w),power=1,sum=1;
  for(int j=0;j<=9;j++){
   if(j){power=power*I(w)/I(j);sum=sum+power;}
   I current=e*sum*I(fact[j]);
   if(b)mass[b-1][j]=prev[j]-current;
   prev[j]=current;tail[j]=current;
  }
 }
}
// Integrals of w^j exp(-w)(1+c*w)^(1/4). Only degrees up to eight occur.
void moments(I c,I m[9]){
 for(int j=0;j<=8;j++)m[j]=I(0, (tail[j]+tail[j+1]).h);
 for(int b=0;b<bins;b++){
  I z=I(1)+c*I(b*.25,(b+1)*.25);
  I weight=root(root(z));
  for(int j=0;j<=8;j++)m[j]=m[j]+weight*mass[b][j];
 }
}
bool check(double left,double right,bool far){
 I x(left,right), x2=x*x, A[5][5]{};
 // n>=12 on y>=3, or n>=2 on y>=64: the analytic bound is below 1e-35.
 for(auto &row:A)for(auto &v:row)v=I(-1e-35,1e-35);
 for(int n=1;n<=(far?1:11);n++){
  int p=n*n; I amp=n==1?I(1):I(p)*expminus(I(p-1)/x2);
  I d=n==1?I(0):I(p-1)/x;
  I m[9];moments(x2/I(p),m);
  for(int i=0;i<5;i++)for(int j=0;j<=i;j++){
   I pol[9]{};
   for(int k=0;k<=j;k++){
    int h=i+j-2*k,degree=0;
    I c[9]{}; c[0]=I(((i+j-k)%2)?-1:1)/I(fact[k]*fact[i-k]*fact[j-k]);
    // Multiply by (p+w*x^2)^k (d+w*x)^h.
    for(int g=0;g<k+h;g++){
     I v=g<k?I(p):d, slope=g<k?x2:x;
     c[degree+1]=c[degree]*slope;
     for(int s=degree;s>0;s--)c[s]=c[s]*v+c[s-1]*slope;
     c[0]=c[0]*v;degree++;
    }
    for(int s=0;s<=degree;s++)pol[s]=pol[s]+c[s];
   }
   I integral=0;for(int s=0;s<=8;s++)integral=integral+pol[s]*m[s];
   A[i][j]=A[i][j]+amp*(pol[0]-x2/I(4*p)*integral);
  }
 }
 // Signs of successive LDL pivots certify all five leading determinants.
 for(int k=0;k<5;k++){
  I pivot=A[k][k];if(k%2 ? !(pivot.h<0) : !(pivot.l>0))return false;
  for(int i=k+1;i<5;i++)for(int j=k+1;j<=i;j++)
   A[i][j]=A[i][j]-A[i][k]*A[j][k]/pivot;
 }
 return true;
}
int leaves=0,deepest=0;
void cover(double a,double b,int depth,bool far){
 if(check(a,b,far)){leaves++;deepest=max(deepest,depth);return;}
 if(depth>=26)throw runtime_error("unresolved interval near x="+to_string(a));
 double mid=(a+b)/2;cover(a,mid,depth+1,far);cover(mid,b,depth+1,far);
}
void verify_tail(int n,int y){
 I first=I(5)*I(4096)*I(30000000000.);
 for(int j=0;j<26;j++)first=first*I(n);
 for(int j=0;j<4;j++)first=first*I(y);
 first=I(2)*first*expminus_point((n*n-1)*y);
 if(!(first.h<1e-35))throw runtime_error("tail bound");
}
int main(){verify_tail(12,3);verify_tail(2,64);init();cover(0,.125,0,true);cover(.125,145./256,0,false);
 cout<<"Certified all five signs; intervals = "<<leaves<<", max depth = "<<deepest<<"\n";
}