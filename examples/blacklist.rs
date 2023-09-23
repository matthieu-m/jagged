//! A simple blacklist example.
//!
//! In this example, there are two threads:
//! -   A Producer thread will intermittently add new black-listed IDs to the HashMap.
//! -   A Consumer thread will "model" a continuous stream of messages coming and for each check their sender against
//!     the black-list.
//!
//! There could be more Consumer threads; for clarity there isn't.
//!
//! In a realistic implementation, the "time" deadline would be an Atomic, so that the publisher could update it.

extern crate crossbeam_utils;
extern crate jagged;

use std::{thread, time};

use jagged::hashmap::{HashHooks, HashMap, HashMapSnapshot};

const NUMBER_ELEMENTS_PER_BATCH: usize = 10;
const NUMBER_BATCHES: usize = 10;

const PACE_TIME: time::Duration = time::Duration::from_millis(100);
const BLACKLIST_TIME: time::Duration = time::Duration::from_millis(300);

//  Mixed-types look-up!
fn is_blacklisted<H: HashHooks>(
    now: &time::Instant,
    id: &str,
    reader: &HashMapSnapshot<'_, String, time::Instant, H>,
) -> bool {
    reader.get(id).map(|deadline| deadline >= now).unwrap_or(false)
}

fn main() {
    let blacklist: HashMap<_, _> = HashMap::new();
    let reader = blacklist.reader();

    crossbeam_utils::thread::scope(|scope| {
        //
        //  Consumer
        //
        scope.spawn(|_| {
            thread::sleep(PACE_TIME);

            let mut blacklisted = 0;

            for _ in 0..NUMBER_BATCHES {
                //  Only periodically renew now & snapshot to amortize cost.
                let now = time::Instant::now();
                let snapshot = reader.snapshot();

                //  Simulate continuous stream of messages
                for i in 0..NUMBER_BATCHES {
                    for j in 0..NUMBER_ELEMENTS_PER_BATCH {
                        let id = i * NUMBER_ELEMENTS_PER_BATCH + j;
                        let id = format!("{}", id);

                        if is_blacklisted(&now, &id, &snapshot) {
                            println!("Consumer - {} is black-listed", id);
                            blacklisted += 1;
                        }
                    }
                }

                thread::sleep(PACE_TIME);
            }

            println!(
                "Consumer - {} messages black-listed from {:?}",
                blacklisted,
                reader.snapshot()
            );

            assert!(blacklisted >= NUMBER_BATCHES * 2);
        });

        //
        //  Producer
        //
        for i in 0..NUMBER_BATCHES {
            for j in 0..NUMBER_ELEMENTS_PER_BATCH {
                let id = i * NUMBER_ELEMENTS_PER_BATCH + j;

                //  "Randomly" blacklist a few elements
                if id * 13 % NUMBER_ELEMENTS_PER_BATCH == 0 {
                    let deadline = time::Instant::now() + BLACKLIST_TIME;

                    blacklist.insert(format!("{}", id), deadline);

                    println!("Producer - black-listing {}", id);
                }
            }

            thread::sleep(PACE_TIME);
        }
    })
    .unwrap();
}
