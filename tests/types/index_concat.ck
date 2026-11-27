module index_concat

# An element of byte strings side by side is the element of the one its
# index falls in.
lemma third xs ys zs ws m : xs~Bytes, ys~Bytes, zs~Bytes, ws~Bytes, m~Nat,
                            len xs + len ys <= m, m < len ws,
                            len ws == len xs + len ys + len zs,
                            ws[m] == zs[m - len xs - len ys]
    ensures (xs ++ ys ++ zs)[m] == ws[m]
