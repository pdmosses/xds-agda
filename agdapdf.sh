DIR="latex/$1"

echo Generating latex files in $DIR
for FILE in $1/*.lagda; do
  agda --latex $FILE
done

echo Generating pdf from latex/$1.tex
cd latex
pdflatex $1.tex
pdflatex $1.tex
cd ..