for file in examples/bench/*; do
    echo "$file:"
    time -p timeout 180 ./test.sh $file
    if [ $? -ne 0 ]; then
        echo "Timeout"
    fi
    echo ""
done
#! /bin/bash
