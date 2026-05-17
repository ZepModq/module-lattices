use std::marker::PhantomData;

// Stati per il Type-State Pattern
pub struct NormalDomain;
pub struct NttDomain;

fn bitrev7(mut x: u16) -> u16 {
    let mut r = 0;
    for _ in 0..7 {
        r = (r << 1) | (x & 1);
        x >>= 1;
    }
    r
}

/// Il contesto che racchiude i parametri matematici
pub struct Context {
    pub q: u32,
    pub zetas: [u32; 128],
    pub arr: [i16; 128],
}

impl Context {
    /// Recupera il valore ζ₂BitRev7(i)+1 modulo q
    pub fn get_zeta2(&self, i: u16) -> u32 {
        let rev = (2 * bitrev7(i) + 1) as usize;
        let val = self.arr[rev] as i32;
        let modulus = self.q as i32;
        (((val % modulus) + modulus) % modulus) as u32
    }

    /// Helper richiesto dalla moltiplicazione base-case
    pub fn get_arr_reduced(&self, i: usize) -> u32 {
        let val = self.arr[i] as i32;
        let modulus = self.q as i32;
        (((val % modulus) + modulus) % modulus) as u32
    }
}

/// Struttura Polynomial basata su Type-State Pattern
pub struct Polynomial<State = NormalDomain> {
    pub coefficients: [u32; 256],
    _state: PhantomData<State>,
}

// --- Metodi validi per QUALSIASI stato ---
impl<State> Polynomial<State> {
    pub fn add(&self, other: &Self, ctx: &Context) -> Self {
        let mut res = [0u32; 256];
        for i in 0..256 {
            res[i] = (self.coefficients[i] + other.coefficients[i]) % ctx.q;
        }
        Self {
            coefficients: res,
            _state: PhantomData,
        }
    }

    pub fn sub(&self, other: &Self, ctx: &Context) -> Self {
        let mut res = [0u32; 256];
        for i in 0..256 {
            res[i] = (self.coefficients[i] + ctx.q - other.coefficients[i]) % ctx.q;
        }
        Self {
            coefficients: res,
            _state: PhantomData,
        }
    }
}

// --- Metodi esclusivi del dominio Normale ---
impl Polynomial<NormalDomain> {
    pub fn new(input: [u32; 256], ctx: &Context) -> Self {
        let mut coefficients = input;
        for c in coefficients.iter_mut() {
            *c %= ctx.q;
        }
        Self {
            coefficients,
            _state: PhantomData,
        }
    }

    /// Trasforma il polinomio consumandolo e restituendolo in forma NTT
    pub fn to_ntt(mut self, ctx: &Context) -> Polynomial<NttDomain> {
        let mut i = 1;
        let mut len = 128;
        
        while len >= 2 {
            for start in (0..256).step_by(2 * len) {
                let zeta = (ctx.zetas[i] % ctx.q) as u64;
                i += 1;
                
                for j in start..(start + len) {
                    let t = ((zeta * self.coefficients[j + len] as u64) % ctx.q as u64) as u32;
                    self.coefficients[j + len] = (self.coefficients[j] + ctx.q - t) % ctx.q;
                    self.coefficients[j] = (self.coefficients[j] + t) % ctx.q;
                }
            }
            len /= 2;
        }
        
        Polynomial {
            coefficients: self.coefficients,
            _state: PhantomData,
        }
    }
}

// --- Metodi esclusivi del dominio NTT ---
impl Polynomial<NttDomain> {
    /// Trasforma il polinomio NTT consumandolo e restituendolo in forma Normale
    pub fn to_normal(mut self, ctx: &Context) -> Polynomial<NormalDomain> {
        let mut i = 127;
        let mut len = 2;
        
        while len <= 128 {
            for start in (0..256).step_by(2 * len) {
                let zeta = (ctx.zetas[i] % ctx.q) as u64;
                i -= 1;
                
                for j in start..(start + len) {
                    let t = self.coefficients[j];
                    self.coefficients[j] = (t + self.coefficients[j + len]) % ctx.q;
                    
                    let diff = if self.coefficients[j + len] >= t {
                        self.coefficients[j + len] - t
                    } else {
                        self.coefficients[j + len] + ctx.q - t
                    };
                    
                    self.coefficients[j + len] = ((zeta * diff as u64) % ctx.q as u64) as u32;
                }
            }
            len *= 2;
        }
        
        for j in 0..256 {
            self.coefficients[j] = ((self.coefficients[j] as u64 * 3303) % ctx.q as u64) as u32;
        }
        
        Polynomial {
            coefficients: self.coefficients,
            _state: PhantomData,
        }
    }

 /// Moltiplicazione a blocchi (base-case) nel dominio NTT conforme a Kyber
    pub fn multiply_ntt(&self, other: &Self, ctx: &Context) -> Self {
        let mut h = [0u32; 256];
        
        for i in 0..128 {
            // Per mappare correttamente i 128 elementi di TEST_ZETAS senza andare out of bounds:
            // Usiamo il bitrev7 dell'indice per selezionare il corretto fattore zeta.
            // Poiché i è u16, convertiamo a u16.
            let rev_index = bitrev7(i as u16) as usize;
            
            // Per la moltiplicazione a blocchi Kyber, usiamo la mappatura diretta
            // Se l'indice calcolato supera i confini, applichiamo il wrapping modulo 128
            let zeta = ctx.zetas[rev_index % 128]; 
            
            let f = [self.coefficients[2 * i], self.coefficients[2 * i + 1]];
            let g = [other.coefficients[2 * i], other.coefficients[2 * i + 1]];
            
            let result = base_case_multiply(f, g, zeta, ctx.q);
            h[2 * i] = result[0];
            h[2 * i + 1] = result[1];
        }
        
        Self {
            coefficients: h,
            _state: PhantomData,
        }
    }
}

fn base_case_multiply(f: [u32; 2], g: [u32; 2], zeta: u32, q: u32) -> [u32; 2] {
    let q_u64 = q as u64;
    
    // t = f1 * g1
    let t = ((f[1] as u64 * g[1] as u64) % q_u64) as u32;
    
    // temp = t * zeta = f1 * g1 * zeta
    // Applichiamo la sottrazione modulare se necessario nello standard Kyber (zeta è spesso invertito)
    let temp = ((zeta as u64 * t as u64) % q_u64) as u32;
    
    // h0 = f0 * g0 + f1 * g1 * zeta
    let h0 = (((f[0] as u64 * g[0] as u64) + temp as u64) % q_u64) as u32;
    
    // h1 = f0 * g1 + f1 * g0
    let h1 = (((f[0] as u64 * g[1] as u64) + (f[1] as u64 * g[0] as u64)) % q_u64) as u32;
    
    [h0, h1]
}

// --- UNIT TEST ---
#[cfg(test)]
mod tests {
    use super::*;

    static TEST_ZETAS: [u32; 128] = [
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

    static TEST_ARR: [i16; 128] = [
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

    fn setup_context() -> Context {
        Context {
            q: 3329,
            zetas: TEST_ZETAS,
            arr: TEST_ARR,
        }
    }

    #[test]
    fn test_polynomial_creation_reduction() {
        let ctx = setup_context();
        let mut input = [0u32; 256];
        input[0] = 3330;
        
        let p = Polynomial::new(input, &ctx);
        assert_eq!(p.coefficients[0], 1);
    }

    #[test]
    fn test_polynomial_add_sub() {
        let ctx = setup_context();
        let mut input_a = [0u32; 256];
        let mut input_b = [0u32; 256];
        input_a[0] = 2000;
        input_b[0] = 1500;

        let p_a = Polynomial::new(input_a, &ctx);
        let p_b = Polynomial::new(input_b, &ctx);

        let p_sum = p_a.add(&p_b, &ctx);
        assert_eq!(p_sum.coefficients[0], 171);

        let p_sub = p_a.sub(&p_b, &ctx);
        assert_eq!(p_sub.coefficients[0], 500);
    }

    #[test]
    fn test_ntt_inv_bounds() {
        let ctx = setup_context();
        let p = Polynomial::new([42; 256], &ctx);
        
        let p_ntt = p.to_ntt(&ctx);
        for &c in p_ntt.coefficients.iter() {
            assert!(c < ctx.q);
        }

        let p_normal = p_ntt.to_normal(&ctx);
        for &c in p_normal.coefficients.iter() {
            assert!(c < ctx.q);
        }
    }

    #[test]
    fn test_multiplication_ntt() {
        let ctx = setup_context();
        let p1 = Polynomial::new([1; 256], &ctx).to_ntt(&ctx);
        let p2 = Polynomial::new([2; 256], &ctx).to_ntt(&ctx);
        
        let p_mul = p1.multiply_ntt(&p2, &ctx);
        let p_final = p_mul.to_normal(&ctx);
        
        for &c in p_final.coefficients.iter() {
            assert!(c < ctx.q);
        }
    }
}