#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

int main()
{
int k;
int l;
int r = 2;
if (l == 0){
r = 3;
l = 2;
assert(0); //by INCEPECTION
exit(1);
k = 5;
assert(0); //by INCEPECTION
}
if (l == 1){
k = 5;
assert(0); //by INCEPECTION
}else{ 
r = 12;
assert(0); //by INCEPECTION
}
int x = 0;
while (x < 10){ 
printf("%d\n", x);
x++;
}
assert(0); //by INCEPECTION
int k1;
for (k1 = 0; k1 < 10; k1++){ 
printf("%d\n", k1);
}
assert(0); //by INCEPECTION
int x1;
x1 = 0;
do {
printf("Hello, world!\n");
} while (x1 != 0);
assert(0); //by INCEPECTION
int w = 0;
for (w = 0; w < 3; w++){
for (w = 0; w < 3; w++){
for (w = 0; w < 3; w++){
x1 = 1;
}
assert(0); //by INCEPECTION
}
assert(0); //by INCEPECTION
}
assert(0); //by INCEPECTION
for (w = 0; w < 3; w++){
if (w){
x1 = 1;
assert(0); //by INCEPECTION
}else{ 
x1 = 0;
assert(0); //by INCEPECTION
}
}
assert(0); //by INCEPECTION
for (w = 0; w < 3; w++){
for (w = 0; w < 3; w++){
if (w){
x1 = 1;
assert(0); //by INCEPECTION
}
}
assert(0); //by INCEPECTION
}
assert(0); //by INCEPECTION
int qw = 5;
switch (qw)
{
case 1: 
qw = 1;
assert(0); //by INCEPECTION
break;
case 2: 
qw = 2;
assert(0); //by INCEPECTION
break;
case 3: 
qw = 3;
assert(0); //by INCEPECTION
break;
case 4: 
qw = 4;
assert(0); //by INCEPECTION
break;
case 5: 
qw = 5;
assert(0); //by INCEPECTION
break;
default: 
qw = 0;
assert(0); //by INCEPECTION
break;
}

int qwa = 5;
switch (qwa)
{
case 1: 
qwa = 1;
assert(0); //by INCEPECTION
case 2: 
qwa = 2;
assert(0); //by INCEPECTION
case 3: 
qwa = 3;
assert(0); //by INCEPECTION
case 4: 
case 5: 
qwa = 5;
assert(0); //by INCEPECTION
default: 
qwa = 0;
assert(0); //by INCEPECTION
}
}

