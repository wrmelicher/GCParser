#!/bin/sh

OUTFILE=`basename $1`.opt
TEMPFILE=.`basename $1`.temp

echo | cat $1 - | tac $1 | python optimize.py - | tac > $TEMPFILE
if [ "$2" != "--no-local" ]
then
    python local_opt.py $TEMPFILE > $OUTFILE
    rm $TEMPFILE
else
    mv $TEMPFILE $OUTFILE
fi

