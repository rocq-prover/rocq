use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    let out = PathBuf::from(env::var("OUT_DIR").unwrap());
    let where_ = match env::var("OCAML_WHERE") {
        Ok(w) => w,
        Err(_) => {
            let o = Command::new("ocamlfind")
                .args(["ocamlc", "-where"])
                .output()
                .expect("cannot find the OCaml standard library directory");
            String::from_utf8(o.stdout).unwrap().trim().to_string()
        }
    };
    let cc = env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let ar = env::var("AR").unwrap_or_else(|_| "ar".to_string());
    let mut objs = vec![];
    for f in ["boxroot", "ocaml_hooks", "platform"] {
        let src = format!("boxroot/{}.c", f);
        let obj = out.join(format!("{}.o", f));
        let st = Command::new(&cc)
            .args(["-O2", "-fPIC", "-std=gnu11", "-c", "-I", &where_, "-I", "boxroot"])
            .arg(&src)
            .arg("-o")
            .arg(&obj)
            .status()
            .expect("failed to run the C compiler");
        assert!(st.success(), "failed to compile {}", src);
        println!("cargo:rerun-if-changed={}", src);
        objs.push(obj);
    }
    let lib = out.join("libboxroot.a");
    let _ = std::fs::remove_file(&lib);
    let st = Command::new(&ar).arg("rcs").arg(&lib).args(&objs).status().unwrap();
    assert!(st.success());
    println!("cargo:rustc-link-search=native={}", out.display());
    println!("cargo:rustc-link-lib=static=boxroot");
    println!("cargo:rerun-if-env-changed=OCAML_WHERE");
}
