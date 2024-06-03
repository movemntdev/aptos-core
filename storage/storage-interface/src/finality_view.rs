use std::sync::RwLock;

use aptos_types::{ledger_info::LedgerInfoWithSignatures, transaction::Version};

use crate::{AptosDbError, DbReader, Result};

/// A wrapper over [`DbReader`], representing ledger at the end of a block
/// as the latest ledger and its version as the latest transaction version.
pub struct FinalityView<Db> {
    reader: Db,
    finalized_ledger_info: RwLock<Option<LedgerInfoWithSignatures>>,
}

impl<Db> FinalityView<Db> {
    pub fn new(reader: Db) -> Self {
        Self {
            reader,
            finalized_ledger_info: RwLock::new(None),
        }
    }
}

impl<Db: DbReader> FinalityView<Db> {
    /// Updates the information on the latest finalized block's ledger.
    pub fn set_finalized_ledger_info(&self, ledger_info: LedgerInfoWithSignatures) -> Result<()> {
        // Sanity checks: finalization should not be set on an empty database,
        // the finality version should not exceed the latest committed.
        match self.reader.get_latest_state_checkpoint_version()? {
            None => return Err(AptosDbError::Other("no ledger states to finalize".into())),
            Some(ver) => {
                let fin_version = ledger_info.ledger_info().version();
                if fin_version > ver {
                    return Err(AptosDbError::Other(format!(
                        "finality version {fin_version} exceeds committed version {ver}"
                    )));
                }
            },
        }

        let mut fin_legder_info = self.finalized_ledger_info.write().unwrap();
        *fin_legder_info = Some(ledger_info);
        Ok(())
    }
}

impl<Db: DbReader> DbReader for FinalityView<Db> {
    fn get_read_delegatee(&self) -> &dyn DbReader {
        &self.reader
    }

    fn get_latest_ledger_info_option(&self) -> Result<Option<LedgerInfoWithSignatures>> {
        let fin_ledger_info = self.finalized_ledger_info.read().unwrap();
        Ok(fin_ledger_info.clone())
    }

    fn get_latest_version(&self) -> Result<Version> {
        let fin_ledger_info = self.finalized_ledger_info.read().unwrap();
        fin_ledger_info
            .as_ref()
            .map(|li| li.ledger_info().version())
            .ok_or_else(|| AptosDbError::NotFound("finalized version".into()))
    }

    fn get_latest_state_checkpoint_version(&self) -> Result<Option<Version>> {
        let fin_ledger_info = self.finalized_ledger_info.read().unwrap();
        let version = fin_ledger_info
            .as_ref()
            .map(|li| li.ledger_info().version());
        Ok(version)
    }

    // TODO: override any other methods needed to maintain the illusion.
}

#[cfg(test)]
mod tests {
    use aptos_types::{aggregate_signature::AggregateSignature, ledger_info::LedgerInfo};

    use super::*;
    use crate::mock::MockDbReaderWriter;

    #[test]
    fn test_get_latest_ledger_info() {
        let view = FinalityView::new(MockDbReaderWriter);
        let ledger_info = view.get_latest_ledger_info_option().unwrap();
        assert_eq!(ledger_info, None);
        let fin_ledger_info =
            LedgerInfoWithSignatures::new(LedgerInfo::dummy(), AggregateSignature::empty());
        view.set_finalized_ledger_info(fin_ledger_info.clone())
            .unwrap();
        let ledger_info = view.get_latest_ledger_info().unwrap();
        assert_eq!(ledger_info, fin_ledger_info);
    }

    #[test]
    fn test_get_latest_version() {
        let view = FinalityView::new(MockDbReaderWriter);
        let res = view.get_latest_version();
        assert!(res.is_err());
        let fin_ledger_info =
            LedgerInfoWithSignatures::new(LedgerInfo::dummy(), AggregateSignature::empty());
        view.set_finalized_ledger_info(fin_ledger_info).unwrap();
        let version = view.get_latest_version().unwrap();
        assert_eq!(version, 0);
    }

    #[test]
    fn test_get_latest_state_checkpoint_version() {
        let view = FinalityView::new(MockDbReaderWriter);
        let version = view.get_latest_state_checkpoint_version().unwrap();
        assert_eq!(version, None);
        let fin_ledger_info =
            LedgerInfoWithSignatures::new(LedgerInfo::dummy(), AggregateSignature::empty());
        view.set_finalized_ledger_info(fin_ledger_info).unwrap();
        let version = view.get_latest_state_checkpoint_version().unwrap();
        assert_eq!(version, Some(0));
    }
}