#! /bin/bash

function verbose (){
    for file in examples/bench/*; do
        echo "$file:"
        time -p timeout 180 ./test.sh $file
        if [ $? -ne 0 ]; then
            echo "Timeout"
        fi
        echo ""
    done
}


function gen_table(){
    # Only shows the "real time"
    TIMEFORMAT='%3R'
    for file in examples/bench/*; do
        # Ignores the output of test.sh
        ret=$( { time timeout 180 ./test.sh $file >/dev/null ; } 2>&1 )
        if [ $? -ne 0 ]; then
            ret="Timeout"
        fi
        echo -e "$(basename -s .imp $file)\t${ret}"
    done
}

case $1 in
    -t)
      gen_table
      ;;
    -*)
      echo "invalid option"
      exit 1
      ;;
    *)
      verbose
      ;;
esac