//Again1.4.a1 and 1.4.a2 are easier ways of doing this.;
//This machine recognizes the intersection of two machines;
//M1 recognizes all strings with an even number of a's;
//M2 recognizes all strings with one or two b's;
title = "14c";
Q = {A0,A1,A2,A3,B0,B1,B2,B3};
S={a,b};
d(A0,a)=B0;
d(A0,b)=A1;
d(B0,a)=A0;
d(B0,b)=B1;
d(A1,a)=B1;
d(A1,b)=A2;
d(B1,a)=A1;
d(B1,b)=B2;
d(A2,a)=B2;
d(A2,b)=A3;
d(B2,a)=A2;
d(B2,b)=B3;
d(A3,a)=B3;
d(A3,b)=A3;
d(B3,a)=A3;
d(B3,b)=B3;
q0 = A0;
F = {A1,A2};