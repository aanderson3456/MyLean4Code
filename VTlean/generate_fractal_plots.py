import os
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.colors as mcolors

# Set styling for premium dark-mode aesthetics
plt.style.use('dark_background')
plt.rcParams['font.family'] = 'sans-serif'
plt.rcParams['font.sans-serif'] = ['DejaVu Sans', 'Arial', 'Helvetica']

def to_binary(val, length):
    # LSB is index 0 (leftmost), MSB is index length-1 (rightmost)
    return tuple((val >> i) & 1 for i in range(length))

def check_sum(v):
    # VT moment: 1-indexed sum of bits from left to right
    return sum((i + 1) * bit for i, bit in enumerate(v))

def del_k(v, k):
    # Set of deletions restricted to the first k bits (0-indexed indices 0 to k-1)
    deletions = set()
    for p in range(k):
        deletion = v[:p] + v[p+1:]
        deletions.add(tuple(deletion))
    return deletions

def generate_matrices(n):
    # Generate all codewords of length n
    r = [to_binary(x, n) for x in range(2**n)]
    # Generate all deletions of length n-1
    v = [to_binary(x, n - 1) for x in range(2**(n-1))]
    
    # Sort stable by VT moment (checksum)
    r.sort(key=check_sum)
    v.sort(key=check_sum)
    
    A = []
    # 1. Compute cumulative deletion matrices A[k] for k in [1, n]
    for k in range(1, n + 1):
        m = []
        for i in range(len(r)):
            d = del_k(r[i], k)
            row = []
            for j in range(len(v)):
                row.append(1 if v[j] in d else 0)
            m.append(row)
        A.append(np.array(m))
        
    # 2. Compute successive deletion differences B[k]
    B = [A[0]]
    for k in range(1, n):
        B.append(A[k] - A[k-1])
        
    return r, v, A, B

def plot_and_save_fractals(n, output_dir):
    os.makedirs(output_dir, exist_ok=True)
    r, v, A, B = generate_matrices(n)
    
    # Identify rows belonging to VTCode(n, 0)
    vt_rows = [i for i, seq in enumerate(r) if check_sum(seq) % (n + 1) == 0]
    
    print(f"n = {n}: VTCode({n}, 0) size = {len(vt_rows)} / {len(r)}")
    
    # Define a vibrant neon palette for the successive bits
    # We use a nice neon color for each bit slice to represent propagation
    neon_colors = [
        '#00f3ff',  # Cyan
        '#ff007f',  # Magenta
        '#ffd700',  # Gold
        '#39ff14',  # Lime Green
        '#ff5e00',  # Orange
        '#8a2be2',  # Blue Violet
        '#00ffcc',  # Turquoise
    ]
    
    # Custom colormaps: 0 is deep dark purple/black, 1 is the vibrant neon color
    cmaps = []
    for c in neon_colors:
        cmap = mcolors.LinearSegmentedColormap.from_list(
            f'custom_{c}', 
            ['#090714', c], 
            N=256
        )
        cmaps.append(cmap)
        
    # 1. Plot individual slices and save high-resolution images
    for k in range(n):
        fig, ax = plt.subplots(figsize=(8, 10), dpi=300)
        
        # Plot B[k] matrix
        im = ax.imshow(B[k], cmap=cmaps[k % len(neon_colors)], interpolation='nearest', aspect='auto')
        
        # Highlight VTCode(n, 0) codewords as horizontal lines
        # Draw subtle gold markers on the y-axis for VT rows to see their geometric placement
        for row in vt_rows:
            ax.axhline(y=row, color='#ffffff', alpha=0.15, linewidth=0.5)
            # Add a small gold dot on the left of the row
            ax.plot(-0.75, row, marker='>', color='#ffd700', markersize=4, clip_on=False)
            
        ax.set_title(f"Bit-by-Bit Deletion-Confusion Fractal B[{k}] (k={k+1})\nLength n={n}, Deletion in Bit {k+1}", fontsize=12, fontweight='bold', color='#ffffff', pad=15)
        ax.set_xlabel(f"Deletions of length {n-1} (Sorted by Checksum)", fontsize=10, labelpad=10)
        ax.set_ylabel(f"Codewords of length {n} (Sorted by Checksum)\n▶ indicates VTCode({n}, 0) row", fontsize=10, labelpad=10)
        
        # Turn off tick labels since they are long, but keep grid markers
        ax.set_xticks([])
        ax.set_yticks([])
        
        # Premium border styling
        for spine in ax.spines.values():
            spine.set_color('#2e2552')
            spine.set_linewidth(1.5)
            
        plt.tight_layout()
        filename = os.path.join(output_dir, f"fractal_n{n}_B{k}.png")
        plt.savefig(filename, bbox_inches='tight', dpi=300, facecolor='#090714')
        plt.close()
        print(f"Saved: {filename}")
        
    # 2. Plot a beautiful combined multi-panel figure for the entire fractal sequence
    fig, axes = plt.subplots(1, n, figsize=(4 * n, 8), dpi=300, sharey=True)
    if n == 1:
        axes = [axes]
        
    for k in range(n):
        ax = axes[k]
        im = ax.imshow(B[k], cmap=cmaps[k % len(neon_colors)], interpolation='nearest', aspect='auto')
        
        # Highlight VT rows
        for row in vt_rows:
            ax.axhline(y=row, color='#ffffff', alpha=0.1, linewidth=0.3)
            if k == 0:
                ax.plot(-0.75, row, marker='>', color='#ffd700', markersize=3, clip_on=False)
                
        ax.set_title(f"B[{k}] (Bit {k+1})", fontsize=12, fontweight='bold', color=neon_colors[k % len(neon_colors)])
        ax.set_xticks([])
        if k == 0:
            ax.set_ylabel(f"Codewords of length {n} (Sorted by Checksum)", fontsize=10)
            # Add some tick marks to show checksum values
            # We can label a few key check_sums
            yticks = []
            yticklabels = []
            prev_cs = -1
            for idx, seq in enumerate(r):
                cs = check_sum(seq)
                if cs != prev_cs and idx % (2**n // 8) == 0:
                    yticks.append(idx)
                    yticklabels.append(f"CS={cs}")
                    prev_cs = cs
            ax.set_yticks(yticks)
            ax.set_yticklabels(yticklabels, fontsize=8, color='#a0a0c0')
        else:
            ax.set_yticks([])
            
        ax.set_xlabel(f"Deletions (len {n-1})", fontsize=9)
        
        for spine in ax.spines.values():
            spine.set_color('#2e2552')
            
    fig.suptitle(f"Bit-by-Bit Deletion-Confusion Fractal Slices (Length n={n})\nSorted by VT moment (checksum) | ▶ indicates VTCode({n}, 0) row", 
                 fontsize=14, fontweight='bold', color='#ffffff', y=0.98)
    plt.tight_layout()
    combined_filename = os.path.join(output_dir, f"fractal_n{n}_combined.png")
    plt.savefig(combined_filename, bbox_inches='tight', dpi=300, facecolor='#090714')
    plt.close()
    print(f"Saved combined plot: {combined_filename}")

if __name__ == '__main__':
    # We will generate and plot for both n = 5 and n = 7
    artifact_dir = "/Users/austinanderson/.gemini/antigravity-ide/brain/51857c0d-a89e-4533-aab0-5985209bf5fb"
    
    print("Generating n = 5 deletion-confusion fractal...")
    plot_and_save_fractals(5, artifact_dir)
    
    print("\nGenerating n = 7 deletion-confusion fractal...")
    plot_and_save_fractals(7, artifact_dir)
    
    print("\nDone! Visual representations successfully generated.")
