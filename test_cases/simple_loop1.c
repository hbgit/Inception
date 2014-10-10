/**
 * gcc -gdwarf-2 simple_loop1.c -o simple_loop1
 * 
 * kvasir-dtrace ./simple_loop1
 * 
 * java daikon.Daikon --config_option daikon.derive.Derivation.disable_derived_variables=true daikon-output/simple_loop1.dtrace
 * 
 * java daikon.PrintInvariants --format acsl --input_code_to_acsl acsl_tests/simple1/simple_loop1.c acsl_tests/simple1/simple_loop1.inv.gz
 * 
 * STATUS: OKAY
 * 
 * */

#include <stdio.h>

int arr[5] = {2,3,1,2,2};

/*@ ensures \result == arr[\result];
*/
int foo(int N){
	
	int i=0;
	while(i < N){
		arr[i] = arr[i] * i;
		i++;
	}
	
	
	return arr[i];
}	

main(){
	
	int a = foo(5);
	
}
