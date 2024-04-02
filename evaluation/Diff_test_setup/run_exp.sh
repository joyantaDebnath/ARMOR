#!/bin/bash

cp -r ../../src/armor-driver/ .
docker build -t armor_tester .
rm -rf armor-driver/

cur=$(pwd)
rm -rf ${cur}/docker_results/
mkdir ${cur}/docker_results/
docker run --privileged -v ${cur}/docker_results:/home/docker_results --rm -it armor_tester
