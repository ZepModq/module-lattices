pub struct Polynomial {
    pub degree: usize,         // The number of coefficients (N)
    pub q: u64,                // The prime modulus for the coefficient ring
    pub coefficients: Vec<u64>,
}


static ZETAS: [u64; 128] = [
    1, 1729, 2580, 3289, 2642, 630, 1897, 848,
    1062, 1919, 193, 797, 2786, 3260, 569, 1746,
    296, 2447, 1339, 1476, 3046, 56, 2240, 1333,
    1426, 2094, 535, 2882, 2393, 2879, 1974, 821,
    289, 331, 3253, 1756, 1197, 2304, 2277, 2055,
    650, 1977, 2513, 632, 2865, 33, 1320, 1915,
    2319, 1435, 807, 452, 1438, 2868, 1534, 2402,
    2647, 2617, 1481, 648, 2474, 3110, 1227, 910,
    17, 2761, 583, 2649, 1637, 723, 2288, 1100,
    1409, 2662, 3281, 233, 756, 2156, 3015, 3050,
    1703, 1651, 2789, 1789, 1847, 952, 1461, 2687,
    939, 2308, 2437, 2388, 733, 2337, 268, 641,
    1584, 2298, 2037, 3220, 375, 2549, 2090, 1645,
    1063, 319, 2773, 757, 2099, 561, 2466, 2594,
    2804, 1092, 403, 1026, 1143, 2150, 2775, 886,
    1722, 1212, 1874, 1029, 2110, 2935, 885, 2154
];
// The real signed ARR array mapped natively to i16 in Rust
static ARR: [i16; 128] = [
    17, -17, 2761, -2761, 583, -583, 2649, -2649,
    1637, -1637, 723, -723, 2288, -2288, 1100, -1100,
    1409, -1409, 2662, -2662, 3281, -3281, 233, -233,
    756, -756, 2156, -2156, 3015, -3015, 3050, -3050,
    1703, -1703, 1651, -1651, 2789, -2789, 1789, -1789,
    1847, -1847, 952, -952, 1461, -1461, 2687, -2687,
    939, -939, 2308, -2308, 2437, -2437, 2388, -2388,
    733, -733, 2337, -2337, 268, -268, 641, -641,
    1584, -1584, 2298, -2298, 2037, -2037, 3220, -3220,
    375, -375, 2549, -2549, 2090, -2090, 1645, -1645,
    1063, -1063, 319, -319, 2773, -2773, 757, -757,
    2099, -2099, 561, -561, 2466, -2466, 2594, -2594,
    2804, -2804, 1092, -1092, 403, -403, 1026, -1026,
    1143, -1143, 2150, -2150, 2775, -2775, 886, -886,
    1722, -1722, 1212, -1212, 1874, -1874, 1029, -1029,
    2110, -2110, 2935, -2935, 885, -885, 2154, -2154
];
impl Polynomial {
    /// Creates a new polynomial, ensuring all coefficients are reduced modulo q.
    pub fn new(coefficients: Vec<u64>, q: u64) -> Self {
        let degree = coefficients.len();
        let mut reduced = coefficients;
        for c in reduced.iter_mut() {
            *c %= q;
        }
        Self {
            degree,
            q,
            coefficients: reduced,
        }
    }

    /// Modular exponentiation: (base^exponent) % modulus
    fn pow_mod(mut base: u64, mut exp: u64, modulus: u64) -> u64 {
        let mut res = 1;
        base %= modulus;
        while exp > 0 {
            if exp % 2 == 1 {
                res = (res as u128 * base as u128 % modulus as u128) as u64;
            }
            base = (base as u128 * base as u128 % modulus as u128) as u64;
            exp /= 2;
        }
        res
    }

    /// Modular inverse using Fermat's Little Theorem (requires q to be prime)
    fn inv_mod(n: u64, modulus: u64) -> u64 {
        Self::pow_mod(n, modulus - 2, modulus)
    }
    pub fn bitrev7(x: u16) -> u16 {
        x.reverse_bits() >> 9
    }
    // Assuming 'zeta_table' is stored or passed to the struct
    pub fn get_zeta2(&self, i: u16, zeta_table: &[u16]) -> u16 {
        let rev = (2 * (i.reverse_bits() >> 9) + 1) as usize;
        // Since we are dealing with u16, a simple % self.q works perfectly
        zeta_table[rev] % (self.q as u16)
    }

    // Port of baseCaseMultiply
    // Replaced Vector2i with a simple, fast fixed-size array [i32; 2]
    pub fn base_case_multiply(&self, f: [i32; 2], g: [i32; 2], zeta: i32) -> [i32; 2] {
        let q_u64 = self.q as u64;
        
        let t = ((f[1] as u64 * g[1] as u64) % q_u64) as i32;
        let temp = ((zeta as u64 * t as u64) % q_u64) as i32;
        
        let mut h0 = (((f[0] as u64 * g[0] as u64) + temp as u64) % q_u64) as i32;
        if h0 < 0 {
            h0 += self.q;
        }
        
        let h1 = (((f[0] as u64 * g[1] as u64) + (f[1] as u64 * g[0] as u64)) % q_u64) as i32;
        
        [h0, h1]
    }

    // Port of addNTTs
    pub fn add_ntts(&self, f: &[i32], g: &[i32]) -> Vec<i32> {
        f.iter()
            .zip(g.iter())
            .map(|(&fi, &gi)| {
                let sum = fi + gi;
                ((sum % self.q) + self.q) % self.q
            })
            .collect()
    }

    // Port of subNTTs
    pub fn sub_ntts(&self, f: &[i32], g: &[i32]) -> Vec<i32> {
        f.iter()
            .zip(g.iter())
            .map(|(&fi, &gi)| {
                let diff = fi - gi;
                ((diff % self.q) + self.q) % self.q
            })
            .collect()
    }

    // Port of multiplyNTTs
    pub fn multiply_ntts(&self, f: &[i32], g: &[i32]) -> Vec<i32> {
        let mut h = vec![0; self.n];
        
        for i in 0..(self.n / 2) {
            let zeta = self.get_zeta2(i as u16);
            
            // Replaces Eigen's .segment<2>(2*i)
            let f_seg = [f[2 * i], f[2 * i + 1]];
            let g_seg = [g[2 * i], g[2 * i + 1]];
            
            let root_factor = ((self.arr[i] % self.q) + self.q) % self.q;
            let result = self.base_case_multiply(f_seg, g_seg, root_factor);
            
            h[2 * i] = result[0];
            h[2 * i + 1] = result[1];
        }
        
        // Final normalization pass
        for val in h.iter_mut() {
            *val = ((*val % self.q) + self.q) % self.q;
        }
        
        h
    }

    // Port of ntt
    pub fn ntt(&self, mut f: Vec<i32>) -> Vec<i32> {
        let mut i = 1;
        let mut len = 128;
        
        while len >= 2 {
            for start in (0..self.n).step_by(2 * len) {
                let zeta = (self.zetas[i] % self.q) as u64;
                i += 1;
                
                for j in start..(start + len) {
                    let t = ((zeta * f[j + len] as u64) % self.q as u64) as i32;
                    f[j + len] = (f[j] + self.q - t) % self.q;
                    f[j] = (f[j] + t) % self.q;
                }
            }
            len /= 2;
        }
        f
    }

    // Port of inv_ntt
    pub fn inv_ntt(&self, f_hat: &[i32]) -> Vec<i32> {
        let mut f = f_hat.to_vec();
        let mut i = 127;
        let mut len = 2;
        
        while len <= 128 {
            for start in (0..self.n).step_by(2 * len) {
                let zeta = (self.zetas[i] % self.q) as u64;
                i -= 1;
                
                for j in start..(start + len) {
                    let t = f[j];
                    f[j] = (t + f[j + len]) % self.q;
                    
                    let diff = if f[j + len] >= t {
                        f[j + len] - t
                    } else {
                        f[j + len] + self.q - t
                    };
                    
                    f[j + len] = ((zeta * diff as u64) % self.q as u64) as i32;
                }
            }
            len *= 2;
        }
        
        // Final scaling layer (3303 is the Kyber constant for 1/256 mod 3329)
        for j in 0..self.n {
            f[j] = ((f[j] as u64 * 3303) % self.q as u64) as i32;
        }
        f
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_creation_and_reduction() {
        // Coefficients [18, 35] with q=17 should be reduced to [1, 1]
        let p = Polynomial::new(vec![18, 35], 17);
        assert_eq!(p.coefficients, vec![1, 1]);
        assert_eq!(p.degree, 2);
    }
    #[test]
    fn test_bit_reversal_7() {
        // Binary: 0000001 (1) -> Reversed 7-bit: 1000000 (64)
        assert_eq!(Polynomial::bitrev7(1), 64);

        // Binary: 0011011 (27) -> Reversed 7-bit: 1101100 (108)
        assert_eq!(Polynomial::bitrev7(27), 108);
    }

    #[test]
    fn test_pow_mod() {
        // 3^4 % 17 = 81 % 17 = 13
        assert_eq!(Polynomial::pow_mod(3, 4, 17), 13);
    }

    #[test]
    fn test_inv_mod() {
        // The modular inverse of 3 mod 17 is 6 (since 3 * 6 = 18 ≡ 1 mod 17)
        assert_eq!(Polynomial::inv_mod(3, 17), 6);
    }

    #[test]
    fn test_ntt_intt_roundtrip() {
        let q = 17;
        let root = 13; // 4th primitive root of unity modulo 17
        let original_coeffs = vec![1, 2, 3, 4];
        
        let mut p = Polynomial::new(original_coeffs.clone(), q);
        
        // Step 1: Transform to frequency domain (NTT)
        p.ntt(root);
        assert_ne!(p.coefficients, original_coeffs); // Coefficients must have changed

        // Step 2: Transform back to time/spatial domain (INTT)
        p.intt(root);

        // Expect to get the exact original coefficients back
        assert_eq!(p.coefficients, original_coeffs);
    }
}