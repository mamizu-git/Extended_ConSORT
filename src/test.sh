./main int $1
z3 ../experiment/out_int.smt2 > ../experiment/result_int 
./main fv $1
z3 ../experiment/out_fv.smt2 > ../experiment/result
./main chc $1
hoice ../experiment/out_chc.smt2 > ../experiment/chc_result
z3 ../experiment/out_chc.smt2 > ../experiment/chc_result_sub
