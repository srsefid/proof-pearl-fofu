#!/bin/sh

tar -czf maxflow.tgz --exclude="maxflow.tgz" --exclude-from=TGZ_EXCLUDE --exclude-tag-all=NOTGZ --exclude-backups --exclude-vcs --transform 's|^|maxflow/|' *
