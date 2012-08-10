#!/bin/sh

echo | cat $1 - | tac $1 | python optimize.py - | tac > .`basename $1`.temp
python local_opt.py .`basename $1`.temp > `basename $1`.opt
rm .`basename $1`.temp
