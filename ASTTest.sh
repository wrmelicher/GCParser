#!/bin/sh

java -ea -cp dist/GCParser.jar frontend.$1 $1

./runtestgcparser $1.cir $1_server.priv $1_client.priv