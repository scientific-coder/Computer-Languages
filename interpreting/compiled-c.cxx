#include <cstdlib>
double f(double a, double b, double c){
  volatile double d=555.666;
  volatile double k;
    for( std::size_t i(1000); i != 0; --i) {
      volatile double e=123.456;
      volatile double f=128.256;
      volatile double g=128.256;
      volatile double h=2.5;
      volatile double j=-1;
      k=d+(e+f+(g-(h+j)));
    }
    return k;
}
int main(int argc, char* argv[]){
  for(std::size_t i(0); i != 10000; ++i)
    {  volatile double d=f(8888., -789., .75); } 
  return 0;
}
