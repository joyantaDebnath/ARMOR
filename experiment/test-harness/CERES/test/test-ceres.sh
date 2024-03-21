#!/bin/bash

for chain in sample-certs/*; do
  echo "$chain"
  ../src/bin/ceres --input $chain --dsl-parser
  ../src/bin/ceres --input $chain --check-proof
  echo ""
done

../src/bin/ceres --version
../src/bin/ceres --check-spec

echo "Finished : test run"
