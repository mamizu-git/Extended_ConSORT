# time -p {
# for i in {1..100}
# do
# ./main int 0
# z3 ../experiment/out_int.smt2 > ../experiment/result_int 
# ./main fv 0
# z3 ../experiment/out_fv.smt2 > ../experiment/result
# ./main chc 0
# hoice ../experiment/out_chc.smt2

# ./main int 1
# z3 ../experiment/out_int.smt2 > ../experiment/result_int 
# ./main fv 1
# z3 ../experiment/out_fv.smt2 > ../experiment/result
# ./main chc 1
# hoice ../experiment/out_chc.smt2

# ./main int 2
# z3 ../experiment/out_int.smt2 > ../experiment/result_int 
# ./main fv 2
# z3 ../experiment/out_fv.smt2 > ../experiment/result
# ./main chc 2
# hoice ../experiment/out_chc.smt2
# done
# }

for ((i=0; i<=$1; i++))
do

./main int $i
z3 ../experiment/out_int.smt2 > ../experiment/result_int 
./main fv $i
z3 ../experiment/out_fv.smt2 > ../experiment/result_$i

done

./main chc $1
hoice ../experiment/out_chc.smt2 > ../experiment/chc_result
