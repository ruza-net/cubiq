#[macro_export]
macro_rules! map {
    ( $($key:expr => $val:expr),* ) => (
        {
            let mut tmp = std::collections::HashMap::new();

            $(
                tmp.insert($key, $val);
            )*

            tmp
        }
    );
}