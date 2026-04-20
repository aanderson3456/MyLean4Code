import sys

def check(M):
    def backtrack(idx, A, mapping):
        if idx == M + 2:
            print(f"M={M} FOUND: {A}")
            return True
            
        for val in range(1, M + 1):
            valid = True
            if idx == M + 1 and val != M: continue
            if idx == M and val != A[0]: continue
            if idx > 0 and idx < M:
                if val == A[0]: continue
                
            new_mapping = mapping.copy()
            if idx > 0:
                dist = val
                prev_val = A[idx-1]
                target_idx = idx - 1 - dist
                
                if dist <= idx - 1:
                    if A[target_idx] != prev_val:
                        valid = False
                    for d in range(1, dist):
                        if A[idx - 1 - d] == prev_val:
                            valid = False
                else:
                    for d in range(1, idx):
                        if A[idx - 1 - d] == prev_val:
                            valid = False
                            
                    if target_idx in new_mapping:
                        if new_mapping[target_idx] != prev_val:
                            valid = False
                    else:
                        new_mapping[target_idx] = prev_val
            
            if valid:
                A.append(val)
                if backtrack(idx + 1, A, new_mapping): return True
                A.pop()
        return False
        
    for start_val in range(1, M+1):
        if backtrack(1, [start_val], {}):
            return True
            
    print(f"M={M} has NO valid sequences! (Contradiction Confirmed)")
    return False

for m in range(2, 6):
    check(m)
