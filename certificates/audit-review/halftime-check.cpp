#include <cstdint>
#include <iostream>
#include "sources/halftime-hash.hpp"
int main(){
 uint64_t a[27]={},b[27]={}; b[6]=1;
 halftime_hash::advanced::Encode3(a); halftime_hash::advanced::Encode3(b);
 unsigned distance=0;
 for(unsigned i=0;i<9;i++) {bool diff=false;for(unsigned j=0;j<3;j++) diff |= a[3*i+j]!=b[3*i+j];distance+=diff;if(diff)std::cout<<"differing symbol "<<i<<'\n';}
 std::cout<<"symbol distance "<<distance<<'\n';
 return distance==1?0:1;
}
