#!/bin/sh

tac $1 | python optimize.py - | tac > `basename $1`.opt
