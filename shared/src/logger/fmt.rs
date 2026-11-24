//! How numbers and times are written in the logs: the same in every
//! one of them.

/// A whole number with a comma between each three digits:
/// `1,000,003`.
pub fn commas(n: u64) -> String {
    let digits = n.to_string();
    let mut out = String::with_capacity(digits.len() + digits.len() / 3);
    for (i, c) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i).is_multiple_of(3) {
            out.push(',');
        }
        out.push(c);
    }
    out
}

/// A number to `places` places of decimals, its whole part with
/// commas: `17,622.6`.
pub fn decimal(x: f64, places: usize) -> String {
    let scale = 10u64.pow(places as u32);
    let scaled = (x.max(0.0) * scale as f64).round() as u64;
    match places {
        0 => commas(scaled),
        _ => format!("{}.{:0places$}", commas(scaled / scale), scaled % scale),
    }
}

/// So many bytes in the unit that fits them: `512 B`, `1.5 KB`,
/// `21.1 MB`, `3.0 GB`. (A thousand to the unit, as the wire counts.)
pub fn bytes(n: u64) -> String {
    match n {
        n if n >= 1_000_000_000 => format!("{} GB", decimal(n as f64 / 1e9, 1)),
        n if n >= 1_000_000 => format!("{} MB", decimal(n as f64 / 1e6, 1)),
        n if n >= 1_000 => format!("{} KB", decimal(n as f64 / 1e3, 1)),
        n => format!("{n} B"),
    }
}

/// How long something has gone on, as hours, minutes and seconds:
/// `0:00:07`, `300:01:00`. The hours go as high as they must.
pub fn uptime(seconds: u64) -> String {
    format!("{}:{:02}:{:02}", seconds / 3600, seconds % 3600 / 60, seconds % 60)
}

/// A length of time in words: `5 seconds`, `1 second`, `0.25 seconds`.
pub fn seconds(millis: u64) -> String {
    match (millis / 1000, millis % 1000) {
        (1, 0) => "1 second".to_string(),
        (s, 0) => format!("{s} seconds"),
        _ => format!("{} seconds", decimal(millis as f64 / 1000.0, 2)),
    }
}

/// A length of time in few letters: `10s`, `1s`, `0.25s`.
pub fn short_seconds(millis: u64) -> String {
    match millis % 1000 {
        0 => format!("{}s", millis / 1000),
        _ => format!("{}s", decimal(millis as f64 / 1000.0, 2)),
    }
}

/// `text`, and then `fill` until it is `width` wide: one `fill` at the
/// least, so that what follows never runs into it.
pub fn column(text: &str, width: usize, fill: char) -> String {
    let have = text.chars().count();
    let mut out = String::with_capacity(width.max(have + 1));
    out.push_str(text);
    out.extend(std::iter::repeat_n(fill, width.saturating_sub(have).max(1)));
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numbers_and_times_are_written_one_way() {
        assert_eq!([commas(0), commas(999), commas(1000), commas(1_000_003)], ["0", "999", "1,000", "1,000,003"]);
        assert_eq!(commas(u64::MAX), "18,446,744,073,709,551,615");
        assert_eq!([decimal(0.0, 1), decimal(0.04, 1), decimal(0.05, 1)], ["0.0", "0.0", "0.1"]);
        assert_eq!([decimal(17_622.56, 1), decimal(1234.5, 0), decimal(0.257, 2)], ["17,622.6", "1,235", "0.26"]);
        assert_eq!(decimal(-3.0, 1), "0.0");
        assert_eq!([bytes(0), bytes(999), bytes(1500), bytes(21_147_120)], ["0 B", "999 B", "1.5 KB", "21.1 MB"]);
        assert_eq!(bytes(3_000_000_000), "3.0 GB");
        assert_eq!([uptime(0), uptime(7), uptime(3661)], ["0:00:00", "0:00:07", "1:01:01"]);
        assert_eq!([uptime(1_080_000), uptime(1_080_060)], ["300:00:00", "300:01:00"]);
        assert_eq!([short_seconds(10_000), short_seconds(1000), short_seconds(250)], ["10s", "1s", "0.25s"]);
        assert_eq!(
            [seconds(5000), seconds(1000), seconds(250), seconds(60_000)],
            ["5 seconds", "1 second", "0.25 seconds", "60 seconds"]
        );
    }

    #[test]
    fn a_column_is_filled_to_its_width_and_never_runs_into_the_next() {
        assert_eq!(column("Requests", 15, '_'), "Requests_______");
        assert_eq!(column("3,000", 15, ' '), "3,000          ");
        assert_eq!(column("", 3, ' '), "   ");
        // Wider than its column: one fill all the same.
        assert_eq!(column("1,000,000,000,000", 15, ' '), "1,000,000,000,000 ");
        assert_eq!(column("exactly fifteen", 15, '_'), "exactly fifteen_");
    }
}
