/*@ requires \valid(v+(0..n-1));
 requires n > 0;
 assigns v[0..n-1];
 ensures \forall integer q; 0<=q<=n-1 ==> v[q]==(unsigned char)0; */
static void make_zero( unsigned char *v, int n ) {

  unsigned char *p = (unsigned char*)v;

  /*@
    loop invariant 0 <= n <= \at(n, Pre);
    loop invariant p == v+(\at(n, Pre)-n);
    loop invariant \forall integer j;  0 <= j < (\at(n, Pre)-n) ==> v[j] == (unsigned char)0;
    loop assigns n, p, v[0..\at(n, Pre)-n-1];
    loop variant n;
  */

  while( n-- ){
    *p++ = 0;
  }
}
