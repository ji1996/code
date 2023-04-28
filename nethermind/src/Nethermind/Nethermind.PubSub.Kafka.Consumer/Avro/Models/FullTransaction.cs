// ------------------------------------------------------------------------------
// <auto-generated>
//    Generated by avrogen, version 1.7.7.5
//    Changes to this file may cause incorrect behavior and will be lost if code
//    is regenerated
// </auto-generated>
// ------------------------------------------------------------------------------

using Avro;
using Avro.Specific;

namespace Nethermind.PubSub.Kafka.Consumer.Avro.Models
{
	public partial class FullTransaction : ISpecificRecord
	{
		public static Schema _SCHEMA = Schema.Parse("{\"type\":\"record\",\"name\":\"FullTransaction\",\"namespace\":\"Nethermind.PubSub.Kafka.Av" +
				"ro.Models\",\"fields\":[{\"name\":\"blockNumber\",\"type\":\"long\"},{\"name\":\"minedAt\",\"typ" +
				"e\":\"long\"},{\"name\":\"tx\",\"type\":{\"type\":\"record\",\"name\":\"Transaction\",\"namespace\"" +
				":\"Nethermind.PubSub.Kafka.Avro.Models\",\"fields\":[{\"name\":\"blockHash\",\"type\":\"str" +
				"ing\"},{\"name\":\"blockNumber\",\"type\":\"long\"},{\"name\":\"fromAddr\",\"type\":\"string\"},{" +
				"\"name\":\"gas\",\"type\":\"long\"},{\"name\":\"gasPrice\",\"type\":\"long\"},{\"name\":\"hash\",\"ty" +
				"pe\":\"string\"},{\"name\":\"input\",\"type\":\"bytes\"},{\"name\":\"nonce\",\"type\":\"int\"},{\"na" +
				"me\":\"toAddr\",\"type\":[\"null\",\"string\"]},{\"name\":\"transactionIndex\",\"type\":\"int\"}," +
				"{\"name\":\"weiValue\",\"type\":\"string\"},{\"name\":\"v\",\"type\":\"int\"},{\"name\":\"r\",\"type\"" +
				":\"string\"},{\"name\":\"s\",\"type\":\"string\"}]}},{\"name\":\"receipt\",\"type\":{\"type\":\"rec" +
				"ord\",\"name\":\"Receipt\",\"namespace\":\"Nethermind.PubSub.Kafka.Avro.Models\",\"fields\"" +
				":[{\"name\":\"blockHash\",\"type\":\"string\"},{\"name\":\"blockNumber\",\"type\":\"long\"},{\"na" +
				"me\":\"contractAddress\",\"type\":[\"null\",\"string\"]},{\"name\":\"cumulativeGasUsed\",\"typ" +
				"e\":\"long\"},{\"name\":\"fromAddr\",\"type\":\"string\"},{\"name\":\"gasUsed\",\"type\":\"long\"}," +
				"{\"name\":\"logs\",\"type\":{\"type\":\"array\",\"items\":{\"type\":\"record\",\"name\":\"Log\",\"nam" +
				"espace\":\"Nethermind.PubSub.Kafka.Avro.Models\",\"fields\":[{\"name\":\"address\",\"type\"" +
				":\"string\"},{\"name\":\"logTopics\",\"type\":{\"type\":\"array\",\"items\":\"string\"}},{\"name\"" +
				":\"data\",\"type\":\"string\"},{\"name\":\"blockNumber\",\"type\":\"long\"},{\"name\":\"transacti" +
				"onHash\",\"type\":\"string\"},{\"name\":\"transactionIndex\",\"type\":\"int\"},{\"name\":\"block" +
				"Hash\",\"type\":\"string\"},{\"name\":\"logIndex\",\"type\":\"int\"},{\"name\":\"removed\",\"type\"" +
				":\"boolean\"}]}}},{\"name\":\"logsBloom\",\"type\":\"string\"},{\"name\":\"status\",\"type\":\"in" +
				"t\"},{\"name\":\"toAddr\",\"type\":[\"null\",\"string\"]},{\"name\":\"transactionHash\",\"type\":" +
				"\"string\"},{\"name\":\"transactionIndex\",\"type\":\"int\"}]}}]}");
		private long _blockNumber;
		private long _minedAt;
		private Transaction _tx;
		private Receipt _receipt;
		public virtual Schema Schema
		{
			get
			{
				return FullTransaction._SCHEMA;
			}
		}
		public long blockNumber
		{
			get
			{
				return this._blockNumber;
			}
			set
			{
				this._blockNumber = value;
			}
		}
		public long minedAt
		{
			get
			{
				return this._minedAt;
			}
			set
			{
				this._minedAt = value;
			}
		}
		public Transaction tx
		{
			get
			{
				return this._tx;
			}
			set
			{
				this._tx = value;
			}
		}
		public Receipt receipt
		{
			get
			{
				return this._receipt;
			}
			set
			{
				this._receipt = value;
			}
		}
		public virtual object Get(int fieldPos)
		{
			switch (fieldPos)
			{
			case 0: return this.blockNumber;
			case 1: return this.minedAt;
			case 2: return this.tx;
			case 3: return this.receipt;
			default: throw new AvroRuntimeException("Bad index " + fieldPos + " in Get()");
			};
		}
		public virtual void Put(int fieldPos, object fieldValue)
		{
			switch (fieldPos)
			{
			case 0: this.blockNumber = (System.Int64)fieldValue; break;
			case 1: this.minedAt = (System.Int64)fieldValue; break;
			case 2: this.tx = (Transaction)fieldValue; break;
			case 3: this.receipt = (Receipt)fieldValue; break;
			default: throw new AvroRuntimeException("Bad index " + fieldPos + " in Put()");
			};
		}
	}
}
