[![Crates.io][crates-badge]][crates-url]
[![License][licence-badge]][licence-url]
[![Test Status][test-badge]][test-url]
[![Documentation][doc-badge]][doc-url]

[crates-badge]: https://img.shields.io/crates/v/rankmap.svg
[crates-url]: https://crates.io/crates/rankmap
[licence-badge]: https://img.shields.io/badge/license-Unlicense-blue.svg
[licence-url]: https://github.com/dapper91/rankmap/blob/master/LICENSE
[test-badge]: https://github.com/dapper91/rankmap/actions/workflows/test.yml/badge.svg?branch=master
[test-url]: https://github.com/dapper91/rankmap/actions/workflows/test.yml
[doc-badge]: https://docs.rs/rankmap/badge.svg
[doc-url]: https://docs.rs/rankmap

# rankmap

Ranked hash table.

A [hash-table](https://en.wikipedia.org/wiki/Hash_table) / [binary-heap](https://en.wikipedia.org/wiki/Binary_heap) 
combined data structure that supports the following operations:

# Time complexity
| [Description]                | [Operation]  | [Complexity] |
|------------------------------|--------------|--------------|
| get value by key             | get          | *O*(1)~      |
| check key existence          | contains_key | *O*(1)~      |
| pop element with lowest rank | pop          | *O*(log(N))  |
| get element with lowest rank | top          | *O*(1)       |
| insert element with rank     | insert       | *O*(log(N))  |
| remove element               | remove       | *O*(log(N))  |

```rust
use std::thread;
use std::time::{Duration, Instant};

use rankmap::RankMap;

fn task1() {
    println!("task1 finished")
}

fn task2() {
    println!("task2 finished")
}

fn task3() {
    println!("task3 finished")
}

fn main() {
    let mut scheduler: RankMap<&str, Box<dyn Fn()>, Instant> = RankMap::new();

    let tank_id = "task1";
    let task = Box::new(task1);
    let run_at = Instant::now() + Duration::from_secs(1);
    scheduler.insert(tank_id, task, run_at);

    let tank_id = "task2";
    let task = Box::new(task2);
    let run_at = Instant::now() + Duration::from_secs(2);
    scheduler.insert(tank_id, task, run_at);

    while let Some((task_name, task, run_at)) = scheduler.pop() {
        let backoff = run_at - Instant::now();
        thread::sleep(backoff);
        println!("executing {}", task_name);
        task();
    }

    let tank_id = "task3";
    let task = Box::new(task3);
    let run_at = Instant::now() + Duration::from_secs(1);
    scheduler.insert(tank_id, task, run_at);

    if let Some((task, run_at)) = scheduler.remove(&"task3") {
        println!("task3 cancelled");
    }

    assert!(scheduler.top().is_none());
}
```

See [documentation](https://docs.rs/rankmap) for more details.
