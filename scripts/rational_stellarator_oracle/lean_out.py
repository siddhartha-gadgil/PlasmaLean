def d3_str(A):
    return " | ".join(" ; ".join(" ".join(str(x) for x in f) for f in B) for B in A)
