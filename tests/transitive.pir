e(0, 1).
e(1, 2).
%e(2, 3).
t(x, y) :- e(x, y).
t(x, z) :- t(x, y), t(y, z).
%t(x, y) :- -(x+y) != z.
%t(x, y)?
