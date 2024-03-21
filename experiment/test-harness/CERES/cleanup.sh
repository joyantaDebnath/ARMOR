#!/bin/bash

rm -rf ~/.ceres/ 2> /dev/null

rm -rf src/build/ 2> /dev/null
rm -rf src/bin/ 2> /dev/null
rm src/ceres.spec 2> /dev/null

echo "Success : CERES clean up"
