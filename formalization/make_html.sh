#!/bin/bash
isabelle build -d. -v Edka_Document
rm -rf html/browser_info/*

cp -a ~/.isabelle/Isabelle2015/browser_info/Unsorted/Edka_Document/* html/browser_info/

./fix_urls.sh html/browser_info
