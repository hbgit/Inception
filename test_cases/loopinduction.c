/**
 * gcc -gdwarf-2 -O0 loopinduction.c -o loopinduction
 * 
 * kvasir-dtrace ./loopinduction
 * 
 * java daikon.Daikon daikon-output/loopinduction.dtrace
 * 
 * Checkout examples from southampton
 * 
 * STATUS: BUG: how work with return == 100
 * 
 * */

#include <stdio.h>
#include <assert.h>

//INV: return == 100

//@ ensures \result == 100;
long long int foo(){
	long long int i = 1 , sn = 0 ;
	unsigned int n = 100;
	
	//assume(n >= 1);
	
	//@ assert n >= 1;
	
	while( i <= n ){
		sn = sn + i ;
		i ++;
	}
	
	return sn;
}

int main( ){
	

	foo();

	//assert( sn == n ) ;	
	// assert \result == 100;
	
	
	

}

