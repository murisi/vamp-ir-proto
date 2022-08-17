e(x, y) :- x=0, y=1.
e(x, y) :- x=1, y=2.
a(x) :- x=11.
%e(2, 3).
%t(x, y) :- e(x, y).
t(x, z) :- a(y), e(x, y), e(y, z).
%t(x, y) :- -(x+y) != z.
t(5, 3)?
