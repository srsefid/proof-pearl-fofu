#!/bin/sh

tar -czf EdmondsKarp_Maxflow.tgz --exclude="Dinic_Maxflow.tgz" --exclude-from=TGZ_EXCLUDE --exclude-tag-all=NOTGZ --exclude-backups --exclude-vcs --transform 's|^|Dinic_Maxflow/|' *
