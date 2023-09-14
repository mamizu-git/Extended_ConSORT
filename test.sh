#! /bin/bash
j=3
while true
do
	./src/main int $1 $j
	z3 experiment/out_int.smt2 > experiment/result_int
	./src/main fv $1 0
	z3 experiment/out_fv.smt2 > experiment/result
	st=`head -n 1 experiment/result`
	if [ $st = "sat" ] ; then
		break
	fi
	j=$(($j+1))
done
echo "range: $j"
echo "ownership: $st"
./src/main chc $1 0
hoice experiment/out_chc.smt2 > experiment/chc_result
st2=`head -n 1 experiment/chc_result` 
echo "refinement: $st2"
echo ""