use dimacs::read_dimacs;

#[test]
fn simple_cnf_serialize_1() {
    let sample = r"
        c Sample DIMACS .cnf file
        c holding some information
        c and trying to be some
        c kind of a test.
        p cnf 42 1337
        1 2 0
        -3 4 0
        5 -6 7 0
        -7 -8 -9 0";
    let comments = vec![
        "Sample DIMACS.cnf file",
        "holding some information",
    ];
    let parsed = read_dimacs(sample.as_bytes()).expect("valid .cnf");
    let mut ser = String::from("");
    parsed.serialize(&comments, &mut ser).unwrap();
    let parsed2 = read_dimacs(ser.as_bytes()).expect("valid .cnf");
    assert_eq!(parsed, parsed2);
}

#[test]
fn simple_cnf_serialize_2() {
    let sample = r"
        c Example CNF format file
        c
        p cnf 4 3
        1 3 -4 0
        4 0 2
        -3";
    let comments = vec![
        "Sample DIMACS.cnf file",
        "holding some information",
    ];
    let parsed = read_dimacs(sample.as_bytes()).expect("valid .cnf");
    let mut ser = String::from("");
    parsed.serialize(&comments, &mut ser).unwrap();
    let parsed2 = read_dimacs(ser.as_bytes()).expect("valid .cnf");
    assert_eq!(parsed, parsed2);
}

#[test]
fn simple_sat_serialize() {
    let sample = r"
        c Sample DIMACS .sat file
        p sat 42
        (*(+(1 3 -4)
        +(4)
        +(2 3)))";
    let comments = vec![];
    let parsed = read_dimacs(sample.as_bytes()).expect("valid .sat");
    let mut ser = String::from("");
    parsed.serialize(&comments, &mut ser).unwrap();
    let parsed2 = read_dimacs(ser.as_bytes()).expect("valid .sat");
    assert_eq!(parsed, parsed2);
}

#[test]
fn xor_sat_serialize() {
    let sample = r"
        c Sample DIMACS .satx file
        p satx 42
        (xor(+(1 3 -4)
        +(4)
        +(2 3)))";
    let comments = vec![];
    let parsed = read_dimacs(sample.as_bytes()).expect("valid .satx");
    let mut ser = String::from("");
    parsed.serialize(&comments, &mut ser).unwrap();
    let parsed2 = read_dimacs(ser.as_bytes()).expect("valid .satx");
    assert_eq!(parsed, parsed2);
}
#[test]
fn xoreq_sat_serialize() {
    let sample = r"
        c Sample DIMACS .satex file
        p satex 42
        (xor(+(1 3 -4)
        +(4)
        =(2 3)))";
    let comments = vec![];
    let parsed = read_dimacs(sample.as_bytes()).expect("valid .satex");
    let mut ser = String::from("");
    parsed.serialize(&comments, &mut ser).unwrap();
    let parsed2 = read_dimacs(ser.as_bytes()).expect("valid .satex");
    assert_eq!(parsed, parsed2);
}
