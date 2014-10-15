#include <stdio.h>
#include <assert.h>

//esbmc --64 --no-library --claim [nth] --no-slice simple_if.c
/**
 * TODO:
 *      (1) Example with break and abort execution
 *      (2) All switch case needs break
 * 
 **/

main(){
	
	int k,l;
	int r = 2;
	
	if(l == 0){
		r = 3;
		l = 2;
		exit();
		k = 5;
	}

	if(l == 1){
	    k = 5;
	}else{
	    r = 12;
	}


	int x = 0;  /* Don't forget to declare variables */

    while ( x < 10 ) { /* While x is less than 10 */
      printf( "%d\n", x );
      x++;             /* Update x so the condition can be met eventually */
    }


    int k1;
    /* The loop goes while k1 < 10, and x increases by one every loop*/
    for ( k1 = 0; k1 < 10; k1++ ) {
        /* Keep in mind that the loop condition checks
           the conditional statement before it loops again.
           consequently, when k1 equals 10 the loop breaks.
           x is updated before the condition is checked. */
        printf( "%d\n", k1 );
    }


    int x1;
    x1 = 0;
    do {
        /* "Hello, world!" is printed at least one time
        even though the condition is false */
        printf( "Hello, world!\n" );
    } while ( x1 != 0 );


    /**
    * ==> Loops aninhados
    **/
    int w = 0;
    for(w=0;w<100;w++){
        for(w=0;w<100;w++){
            for(w=0;w<100;w++){
                w = 1;
            }
        }
    }

    /**
    * ==> Condition struture (IF, ELSE) inside Loop
    **/
    for(w=0;w<100;w++){
        if(w){
            w = 1;
        }else{
            w = 0;
        }
    }

    for(w=0;w<100;w++){
        for(w=0;w<100;w++){
            if(w){
                w = 1;
            }
        }
    }



    // switch with break
    int qw = 5;
    switch( qw ){
        case 1:
            qw = 1;
            break;
        case 2:
            qw = 2;
            break;
        case 3:
            qw = 3;
            break;
        case 4:
            qw = 4;
            break;
        case 5:
            qw = 5;
            break;
        default:
            qw = 0;
            break;
    }


    // switch with NO breaks
    int qw = 5;
    switch( qw ){
        case 1:
            qw = 1;
        case 2:
            qw = 2;
        case 3:
            qw = 3;
        case 4:
        case 5:
            qw = 5;
        default:
            qw = 0;
    }
}
