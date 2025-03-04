DIR="docs/$1"

echo Generating html files in fresh $DIR/html
rm -f $DIR/html/* 2> /dev/null
agda --html --html-highlight=all --html-dir=$DIR/html $1/All.lagda

echo Generating md files in $DIR
for FILE in $DIR/html/*.html; do
  MD=${FILE/%\.html/.md}
  sed -e '1d' -e '2 s!.*<body>!!' -e '$ s!</body>.*!!' $FILE > $MD
  mv -f $MD $DIR
done