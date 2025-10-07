#!/bin/bash
echo `grep "core(conjecture" $1 | sed "s/core[(]conjecture,[[]a//;s/[]]).//;s/core[(]conjecture,[[]//" | sed "s/, a/ /g;s/o_/./g;s/i_/'/g;s/u_/_/g"`
