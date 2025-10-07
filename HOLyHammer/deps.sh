#!/bin/bash
echo `grep file $1 | grep -v conjecture | sed "s/.*'.*', *a\([a-zA-Z0-9_]*\)))./\1/" | sed "s/o_/./g;s/i_/'/g;s/u_/_/g" | sed "s/_monomorphized[0-9]*//g" | sort | uniq | tr '\n' ' '`
