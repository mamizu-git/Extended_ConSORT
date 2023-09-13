for file in examples/bench/*; do
    echo "$file:"
    ./test.sh $file
    echo ""
done
