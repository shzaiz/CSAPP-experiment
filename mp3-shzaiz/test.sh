for i in {01..16}; do
    make test$i > tmp1.txt
    make rtest$i > tmp2.txt
    diff tmp1.txt tmp2.txt
    read
done
