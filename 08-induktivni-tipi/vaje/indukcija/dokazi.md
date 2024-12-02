# Dokaz (2)

## Indukcija po xs


    1. d([] @ ys) = d([]) + d(ys)
    ------------------------------
    (1), (5)
    d(ys) = 0 + d(ys)


    2. d((x :: xs) @ ys) = d(x :: xs) + d(ys)
    -----------------------------
    (2)
    d(x::(xs @ ys)) = d(x :: xs) + d(ys)
    (6)
    1 + d(xs @ ys) = (1 + d(xs)) + d(ys)
    (ip)
    1 + (d(xs) + d(ys)) = (1 + d(xs)) + d(ys)
    (asoc)