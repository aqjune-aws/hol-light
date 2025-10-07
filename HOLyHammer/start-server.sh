#!/bin/bash

if [ ! -d "$HOLLIGHT_DIR" ]; then
  echo "Environment variable HOLLIGHT_DIR is not set."
  echo "Please do 'export HOLLIGHT_DIR=<the path to your hol-light>"
  exit 1
fi

cd "$HOLLIGHT_DIR"
HOLyHammer/Snow_v3.2/snow -train -I HOLyHammer/inp.hum -F HOLyHammer/net.hum -B :0-$[$(cat HOLyHammer/deps.all | wc -l)-1]
HOLyHammer/Snow_v3.2/snow -server 60000 -o allboth -F HOLyHammer/net.hum -B :0-$[$(cat HOLyHammer/deps.all | wc -l)-1]
