make TestD := con ['done] : Desc ;
make Test := (Mu TestD) : Set ;
make add : Test -> Test ;
lambda x ;
elim elimOp TestD x ;
ind Test ;
show state ;
