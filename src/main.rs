mod polynomial;
use polynomial::Polynomial;

fn main() {
    let q =3329 ;
    let primitive_root = 13; // For N = 4 coefficients
    
    let mut p = Polynomial::new(vec![1, 2, 3, 4], q);
    
    println!("Original Polynomial: {:?}", p.coefficients);
    
    p.ntt(primitive_root);
    println!("After NTT (Frequency): {:?}", p.coefficients);
    
    p.intt(primitive_root);
    println!("After INTT (Spatial):    {:?}", p.coefficients);
}