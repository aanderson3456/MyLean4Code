def check_seq(P):
    seq = [0] * (2*P + 4)
    def backtrack(idx):
        if idx == 2*P + 4:
            for k in range(P+4):
                if seq[k] != seq[k+P]:
                    return False
            for k in range(1, P+4):
                if seq[P+k] == 0 or seq[P+k] == 2:
                    return False
            return True
            
        if idx == 0:
            seq[idx] = 0
            if backtrack(idx+1): return True
        else:
            val = seq[idx-1]
            found = -1
            for j in range(idx-2, -1, -1):
                if seq[j] == val:
                    found = j
                    break
            if found == -1:
                seq[idx] = 0
            else:
                seq[idx] = idx - 1 - found
                
            if idx > P and (seq[idx] == 0 or seq[idx] == 2):
                return False
                
            if backtrack(idx+1): return True
        return False

    return backtrack(0)

for P in range(1, 31):
    if check_seq(P):
        print(f"Found bounded period for P={P}")
    else:
        print(f"No bounded period for P={P}")
