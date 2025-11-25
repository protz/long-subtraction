type BigInt = [u64; 4];

type Borrow = u8;

fn sub_borrow(b0: Borrow, src1: u64, src2: u64, dst: &mut u64) -> Borrow {
    // tmp = src1 - b_in
    let tmp1 = src1.wrapping_sub(b0 as u64);
    let b1: Borrow = if tmp1 > src1 { 1 } else { 0 };
    let tmp2 = tmp1.wrapping_sub(src2);
    let b2: Borrow = if tmp2 > tmp1 { 1 } else { 0 };
    *dst = tmp2;
    b1 + b2
}

fn sub(b0: Borrow, src1: &BigInt, src2: &BigInt, dst: &mut BigInt) -> Borrow {
    let b1 = sub_borrow(b0, src1[0], src2[0], &mut dst[0]);
    let b2 = sub_borrow(b1, src1[1], src2[1], &mut dst[1]);
    let b3 = sub_borrow(b2, src1[2], src2[2], &mut dst[2]);
    let b4 = sub_borrow(b3, src1[3], src2[3], &mut dst[3]);
    b4
}

fn main() {
    let test1: BigInt = [1, 2, 3, 4];
    let test2: BigInt = [2, 1, 2, 3];
    let mut test3: BigInt = [0; 4];
    let b = sub(0, &test1, &test2, &mut test3);
    assert_eq!(test3, [ -1i64 as u64, 0, 1, 1 ]);
    assert_eq!(b, 0);
}
