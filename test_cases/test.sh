#!/usr/bin/env bash

function compile() {
  ../_build/default/src/codegen.exe --allocator=naive -i "$1/$1.ir" -o "$1/$1-naive.s" >/dev/null
  ../_build/default/src/codegen.exe --allocator=graph -i "$1/$1.ir" -o "$1/$1-graph.s" >/dev/null
}

function run_test_case() {
    spim -f "$1/$1-naive.s" <"$1/$2.in" | tail -n +2 >"$1/$2-naive.out"
    spim -f "$1/$1-graph.s" <"$1/$2.in" | tail -n +2 >"$1/$2-graph.out"
    if cmp -s "$1/$2.out" "$1/$2-naive.out" && cmp -s "$1/$2.out" "$1/$2-graph.out"
    then
      echo "Passed test $1-$2"
    else
      echo "Failed test $1-$2"
    fi
}

function run_test() {
  for i in {0..9}
  do
    run_test_case $1 $i &
  done
  wait
}

function go() {
  compile $1
  run_test $1
}

for prog in bfs fib pow prime quicksort
do
  go $prog &
done
wait
