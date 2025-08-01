namespace IronRSLClient
{
    using System;
    using System.Collections.Generic;
    using System.IO;
    using System.Net;
    using System.Runtime.InteropServices;
    using System.Threading;
    using System.Linq;
    using System.Threading.Tasks;
    using System.Diagnostics;

    // public class VectorClock
    // {
    //     private ulong[] clock;

    //     public int Length => clock.Length;

    //     public VectorClock(int size)
    //     {
    //         clock = new ulong[size];
    //     }

    //     public VectorClock(ulong[] values)
    //     {
    //         clock = (ulong[])values.Clone();
    //     }

    //     public ulong this[int idx]
    //     {
    //         get => clock[idx];
    //         set => clock[idx] = value;
    //     }

    //     public void Merge(VectorClock other)
    //     {
    //         int len = Math.Max(clock.Length, other.clock.Length);
    //         Array.Resize(ref clock, len);

    //         for (int i = 0; i < len; i++)
    //         {
    //             ulong v1 = (i < clock.Length) ? clock[i] : 0;
    //             ulong v2 = (i < other.clock.Length) ? other.clock[i] : 0;
    //             clock[i] = Math.Max(v1, v2);
    //         }
    //     }


    //     public byte[] Marshall()
    //     {
    //         using (MemoryStream ms = new MemoryStream())
    //         {
    //             foreach (var v in clock)
    //             {
    //                 ulong safeVal = v < 0xffff_ffff_ffff_ffff
    //                     ? v
    //                     : 0xffff_ffff_ffff_ffff;

    //                 byte[] bytes = BitConverter.GetBytes(safeVal);
    //                 if (BitConverter.IsLittleEndian)
    //                     Array.Reverse(bytes);

    //                 ms.Write(bytes, 0, bytes.Length);
    //             }
    //             return ms.ToArray();
    //         }
    //     }

    //     public static VectorClock Parse(byte[] data)
    //     {
    //         if (data.Length % 8 != 0)
    //             throw new InvalidDataException("VectorClock data length must be multiple of 8");

    //         int count = data.Length / 8;
    //         ulong[] values = new ulong[count];

    //         for (int i = 0; i < count; i++)
    //         {
    //             byte[] element = new byte[8];
    //             Buffer.BlockCopy(data, i * 8, element, 0, 8);
    //             if (BitConverter.IsLittleEndian)
    //                 Array.Reverse(element);
    //             values[i] = BitConverter.ToUInt64(element, 0);
    //         }

    //         return new VectorClock(values);
    //     }

    //     public VectorClock Clone() => new VectorClock(clock);

    // }

    // public class Dependency
    // {
    //     private Dictionary<ulong, VectorClock> dep = new Dictionary<ulong, VectorClock>();

    //     public Dictionary<ulong, VectorClock> Data => dep;

    //     public Dependency() { }

    //     public Dependency(Dictionary<ulong, VectorClock> initial)
    //     {
    //         dep = new Dictionary<ulong, VectorClock>(initial);
    //     }

    //     public void Merge(Dependency other)
    //     {
    //         foreach (var kv in other.dep)
    //         {
    //             ulong key = kv.Key;
    //             VectorClock otherVc = kv.Value;

    //             if (!dep.ContainsKey(key))
    //             {
    //                 dep[key] = otherVc.Clone();
    //             }
    //             else
    //             {
    //                 dep[key].Merge(otherVc);
    //             }
    //         }
    //     }

    //     public byte[] Marshall()
    //     {
    //         using (MemoryStream ms = new MemoryStream())
    //         {
    //             foreach (var kv in dep)
    //             {
    //                 ulong key = kv.Key < 0xffff_ffff_ffff_ffff
    //                     ? kv.Key
    //                     : 0xffff_ffff_ffff_ffff;

    //                 byte[] keyBytes = BitConverter.GetBytes(key);
    //                 if (BitConverter.IsLittleEndian)
    //                     Array.Reverse(keyBytes);
    //                 ms.Write(keyBytes, 0, keyBytes.Length);

    //                 byte[] vcBytes = kv.Value.Marshall();

    //                 byte[] lenBytes = BitConverter.GetBytes((ulong)vcBytes.Length);
    //                 if (BitConverter.IsLittleEndian)
    //                     Array.Reverse(lenBytes);
    //                 ms.Write(lenBytes, 0, lenBytes.Length);

    //                 ms.Write(vcBytes, 0, vcBytes.Length);
    //             }

    //             return ms.ToArray();
    //         }
    //     }


    //     public static Dependency Parse(byte[] data)
    //     {
    //         Dependency result = new Dependency();
    //         int offset = 0;

    //         while (offset < data.Length)
    //         {
    //             // 1. key
    //             byte[] keyBytes = new byte[8];
    //             Buffer.BlockCopy(data, offset, keyBytes, 0, 8);
    //             if (BitConverter.IsLittleEndian)
    //                 Array.Reverse(keyBytes);
    //             ulong key = BitConverter.ToUInt64(keyBytes, 0);
    //             offset += 8;

    //             // 2. vector clock len
    //             byte[] lenBytes = new byte[8];
    //             Buffer.BlockCopy(data, offset, lenBytes, 0, 8);
    //             if (BitConverter.IsLittleEndian)
    //                 Array.Reverse(lenBytes);
    //             ulong vcLength = BitConverter.ToUInt64(lenBytes, 0);
    //             offset += 8;

    //             // 3. vector clock
    //             byte[] vcBytes = new byte[vcLength];
    //             Buffer.BlockCopy(data, offset, vcBytes, 0, (int)vcLength);
    //             offset += (int)vcLength;

    //             // 4. parse vector clock
    //             result.dep[key] = VectorClock.Parse(vcBytes);
    //         }

    //         return result;
    //     }

    // }

    // public class Meta
    // {
    //     public ulong Key { get; private set; }
    //     public VectorClock Vc { get; private set; }
    //     public Dependency Deps { get; private set; }

    //     public Meta(ulong key, VectorClock vc, Dependency deps)
    //     {
    //         Key = key;
    //         Vc = vc;
    //         Deps = deps;
    //     }

    //     public byte[] Marshall()
    //     {
    //         using (MemoryStream ms = new MemoryStream())
    //         {
    //             ulong safeKey = Key < 0xffff_ffff_ffff_ffff
    //                 ? Key
    //                 : 0xffff_ffff_ffff_ffff;
    //             if (Key >= 0xffff_ffff_ffff_ffff)
    //                 Console.WriteLine("Marshall CMeta overflow");

    //             byte[] keyBytes = BitConverter.GetBytes(safeKey);
    //             if (BitConverter.IsLittleEndian)
    //                 Array.Reverse(keyBytes);
    //             ms.Write(keyBytes, 0, keyBytes.Length);

    //             byte[] vcBytes = Vc.Marshall();

    //             byte[] vcLenBytes = BitConverter.GetBytes((ulong)vcBytes.Length);
    //             if (BitConverter.IsLittleEndian)
    //                 Array.Reverse(vcLenBytes);
    //             ms.Write(vcLenBytes, 0, vcLenBytes.Length);

    //             ms.Write(vcBytes, 0, vcBytes.Length);

    //             byte[] depBytes = Deps.Marshall();

    //             byte[] depLenBytes = BitConverter.GetBytes((ulong)depBytes.Length);
    //             if (BitConverter.IsLittleEndian)
    //                 Array.Reverse(depLenBytes);
    //             ms.Write(depLenBytes, 0, depLenBytes.Length);

    //             ms.Write(depBytes, 0, depBytes.Length);

    //             return ms.ToArray();
    //         }
    //     }

    //     public static Meta Parse(byte[] data)
    //     {
    //         int offset = 0;

    //         byte[] keyBytes = new byte[8];
    //         Buffer.BlockCopy(data, offset, keyBytes, 0, 8);
    //         if (BitConverter.IsLittleEndian)
    //             Array.Reverse(keyBytes);
    //         ulong key = BitConverter.ToUInt64(keyBytes, 0);
    //         offset += 8;

    //         byte[] vcLenBytes = new byte[8];
    //         Buffer.BlockCopy(data, offset, vcLenBytes, 0, 8);
    //         if (BitConverter.IsLittleEndian)
    //             Array.Reverse(vcLenBytes);
    //         ulong vcLength = BitConverter.ToUInt64(vcLenBytes, 0);
    //         offset += 8;

    //         byte[] vcBytes = new byte[vcLength];
    //         Buffer.BlockCopy(data, offset, vcBytes, 0, (int)vcLength);
    //         offset += (int)vcLength;
    //         VectorClock vc = VectorClock.Parse(vcBytes);

    //         // 3. Dependency 长度
    //         byte[] depLenBytes = new byte[8];
    //         Buffer.BlockCopy(data, offset, depLenBytes, 0, 8);
    //         if (BitConverter.IsLittleEndian)
    //             Array.Reverse(depLenBytes);
    //         ulong depLength = BitConverter.ToUInt64(depLenBytes, 0);
    //         offset += 8;

    //         // Dependency 内容
    //         byte[] depBytes = new byte[depLength];
    //         Buffer.BlockCopy(data, offset, depBytes, 0, (int)depLength);
    //         offset += (int)depLength;
    //         Dependency deps = Dependency.Parse(depBytes);

    //         return new Meta(key, vc, deps);
    //     }

    //     public override string ToString()
    //     {
    //         return $"Meta(key={Key}, vc={Vc}, deps={Deps})";
    //     }
    // }

    // public class Local
    // {
    //     private Dictionary<ulong, Meta> local = new Dictionary<ulong, Meta>();
    //     public Dictionary<ulong, Meta> Data => local;

    //     public Local() { }

    //     public Local(Dictionary<ulong, Meta> initial)
    //     {
    //         local = new Dictionary<ulong, Meta>(initial);
    //     }

    //     public byte[] Marshall()
    //     {
    //         using (MemoryStream ms = new MemoryStream())
    //         {
    //             // 1. 写 Local 的 entry 数量 (8字节 big-endian)
    //             byte[] countBytes = BitConverter.GetBytes((ulong)local.Count);
    //             if (BitConverter.IsLittleEndian)
    //                 Array.Reverse(countBytes);
    //             ms.Write(countBytes, 0, countBytes.Length);

    //             // 2. 每个 entry 序列化为 VTuple(key, Meta)
    //             foreach (var kv in local)
    //             {
    //                 // 序列化 key
    //                 ulong key = kv.Key < 0xffff_ffff_ffff_ffff
    //                     ? kv.Key
    //                     : 0xffff_ffff_ffff_ffff;

    //                 byte[] keyBytes = BitConverter.GetBytes(key);
    //                 if (BitConverter.IsLittleEndian)
    //                     Array.Reverse(keyBytes);
    //                 ms.Write(keyBytes, 0, keyBytes.Length);

    //                 // 序列化 Meta
    //                 byte[] metaBytes = kv.Value.Marshall();

    //                 // 写 Meta 长度 (8字节 big-endian)
    //                 byte[] metaLenBytes = BitConverter.GetBytes((ulong)metaBytes.Length);
    //                 if (BitConverter.IsLittleEndian)
    //                     Array.Reverse(metaLenBytes);
    //                 ms.Write(metaLenBytes, 0, metaLenBytes.Length);

    //                 ms.Write(metaBytes, 0, metaBytes.Length);
    //             }

    //             return ms.ToArray();
    //         }
    //     }
 
    //     public static Local Parse(byte[] data)
    //     {
    //         Local result = new Local();
    //         int offset = 0;

    //         // 1. 读取 entry 数量
    //         byte[] countBytes = new byte[8];
    //         Buffer.BlockCopy(data, offset, countBytes, 0, 8);
    //         if (BitConverter.IsLittleEndian)
    //             Array.Reverse(countBytes);
    //         ulong count = BitConverter.ToUInt64(countBytes, 0);
    //         offset += 8;

    //         // 2. 循环解析每个 entry
    //         for (ulong i = 0; i < count; i++)
    //         {
    //             // key
    //             byte[] keyBytes = new byte[8];
    //             Buffer.BlockCopy(data, offset, keyBytes, 0, 8);
    //             if (BitConverter.IsLittleEndian)
    //                 Array.Reverse(keyBytes);
    //             ulong key = BitConverter.ToUInt64(keyBytes, 0);
    //             offset += 8;

    //             // meta 长度
    //             byte[] metaLenBytes = new byte[8];
    //             Buffer.BlockCopy(data, offset, metaLenBytes, 0, 8);
    //             if (BitConverter.IsLittleEndian)
    //                 Array.Reverse(metaLenBytes);
    //             ulong metaLength = BitConverter.ToUInt64(metaLenBytes, 0);
    //             offset += 8;

    //             // meta 内容
    //             byte[] metaBytes = new byte[metaLength];
    //             Buffer.BlockCopy(data, offset, metaBytes, 0, (int)metaLength);
    //             offset += (int)metaLength;

    //             Meta meta = Meta.Parse(metaBytes);
    //             result.Data[key] = meta;
    //         }

    //         return result;
    //     }

    //     public override string ToString()
    //     {
    //         List<string> entries = new List<string>();
    //         foreach (var kv in local)
    //         {
    //             entries.Add($"{kv.Key} => {kv.Value}");
    //         }
    //         return "{" + string.Join(", ", entries) + "}";
    //     }
    // }

    public class VectorClock
    {
        public ulong[] Clock;

        public VectorClock(ulong[] clock)
        {
            Clock = clock;
        }

        public void Merge(VectorClock other)
        {
            int len = Math.Max(Clock.Length, other.Clock.Length);
            ulong[] merged = new ulong[len];
            for (int i = 0; i < len; i++)
            {
                ulong v1 = (i < Clock.Length) ? Clock[i] : 0;
                ulong v2 = (i < other.Clock.Length) ? other.Clock[i] : 0;
                merged[i] = Math.Max(v1, v2);
            }
            Clock = merged;
        }

        public byte[] Marshall()
        {
            using (MemoryStream ms = new MemoryStream())
            {
                MessageBase.EncodeUlong(ms, (ulong)Clock.Length);
                foreach (var v in Clock)
                    MessageBase.EncodeUlong(ms, v);
                return ms.ToArray();
            }
        }

        public static VectorClock Parse(byte[] data, ref int offset)
        {
            ulong len = MessageBase.DecodeUlong(data, ref offset);
            ulong[] clock = new ulong[len];
            for (ulong i = 0; i < len; i++)
                clock[i] = MessageBase.DecodeUlong(data, ref offset);
            return new VectorClock(clock);
        }
    }

    public class Dependency
    {
        public Dictionary<ulong, VectorClock> dep = new Dictionary<ulong, VectorClock>();

        public Dependency() { }

        public Dependency(Dictionary<ulong, VectorClock> existing)
        {
            dep = existing;
        }

        public void Merge(Dependency other)
        {
            foreach (var kv in other.dep)
            {
                if (!dep.ContainsKey(kv.Key))
                    dep[kv.Key] = new VectorClock((ulong[])kv.Value.Clock.Clone());
                else
                    dep[kv.Key].Merge(kv.Value);
            }
        }

        public byte[] Marshall()
        {
            using (MemoryStream ms = new MemoryStream())
            {
                // ✅ 写 Array 长度
                MessageBase.EncodeUlong(ms, (ulong)dep.Count);

                foreach (var kv in dep)
                {
                    // ❌ 删除这行：MessageBase.EncodeUlong(ms, 2);
                    // ✅ Tuple直接序列化内容，无长度前缀
                    
                    MessageBase.EncodeUlong(ms, kv.Key);

                    // VectorClock Array
                    byte[] vcBytes = kv.Value.Marshall();
                    ms.Write(vcBytes, 0, vcBytes.Length);
                }

                return ms.ToArray();
            }
        }

        public static Dependency Parse(byte[] data, ref int offset)
        {
            ulong arrayLen = MessageBase.DecodeUlong(data, ref offset);
            Dependency d = new Dependency();

            for (ulong i = 0; i < arrayLen; i++)
            {
                // ❌ 删除这行：ulong tupleLen = MessageBase.DecodeUlong(data, ref offset);
                // ❌ 删除检查：if (tupleLen != 2) throw...
                // ✅ 直接解析tuple内容
                
                ulong key = MessageBase.DecodeUlong(data, ref offset);
                VectorClock vc = VectorClock.Parse(data, ref offset);
                d.dep[key] = vc;
            }

            return d;
        }
    }

    public class Meta
    {
        public ulong Key;
        public VectorClock Vc;
        public Dependency Deps;

        public Meta(ulong key, VectorClock vc, Dependency deps)
        {
            Key = key;
            Vc = vc;
            Deps = deps;
        }

        public byte[] Marshall()
        {
            using (MemoryStream ms = new MemoryStream())
            {
                // ❌ 删除这行：MessageBase.EncodeUlong(ms, 3);
                // ✅ Tuple直接序列化内容，无长度前缀

                MessageBase.EncodeUlong(ms, Key);
                
                byte[] vcBytes = Vc.Marshall();
                ms.Write(vcBytes, 0, vcBytes.Length);
                
                byte[] depsBytes = Deps.Marshall();
                ms.Write(depsBytes, 0, depsBytes.Length);

                return ms.ToArray();
            }
        }

        public static Meta Parse(byte[] data, ref int offset)
        {
            // ❌ 删除这行：ulong tupleLen = MessageBase.DecodeUlong(data, ref offset);
            // ❌ 删除检查：if (tupleLen != 3) throw...
            // ✅ 直接解析tuple内容

            ulong key = MessageBase.DecodeUlong(data, ref offset);
            VectorClock vc = VectorClock.Parse(data, ref offset);
            Dependency deps = Dependency.Parse(data, ref offset);
            return new Meta(key, vc, deps);
        }
    }

    public class Local
    {
        public Dictionary<ulong, Meta> Data = new Dictionary<ulong, Meta>();

        public Local() { }

        public Local(Dictionary<ulong, Meta> existing)
        {
            Data = existing;
        }

        public byte[] Marshall()
        {
            using (MemoryStream ms = new MemoryStream())
            {
                // ✅ 写 Array 长度
                MessageBase.EncodeUlong(ms, (ulong)Data.Count);

                foreach (var kv in Data)
                {
                    // ❌ 删除这行：MessageBase.EncodeUlong(ms, 2);
                    // ✅ Tuple直接序列化内容，无长度前缀

                    MessageBase.EncodeUlong(ms, kv.Key);

                    // Meta
                    byte[] metaBytes = kv.Value.Marshall();
                    ms.Write(metaBytes, 0, metaBytes.Length);
                }

                return ms.ToArray();
            }
        }

        public static Local Parse(byte[] data, ref int offset)
        {
            ulong arrayLen = MessageBase.DecodeUlong(data, ref offset);
            Local l = new Local();

            for (ulong i = 0; i < arrayLen; i++)
            {
                // ❌ 删除这行：ulong tupleLen = MessageBase.DecodeUlong(data, ref offset);
                // ❌ 删除检查：if (tupleLen != 2) throw...
                // ✅ 直接解析tuple内容

                ulong key = MessageBase.DecodeUlong(data, ref offset);
                Meta meta = Meta.Parse(data, ref offset);
                l.Data[key] = meta;
            }

            return l;
        }
    }






    
    public class HiResTimer
    {
        private static Stopwatch _stopWatch = null;
        public static long Ticks
        {
            get
            {
                return _stopWatch.ElapsedTicks;
            }
        }
        public static void Initialize()
        {
            _stopWatch = Stopwatch.StartNew();
        }
        public static double TicksToMilliseconds(long ticks)
        {
            return ticks * 1000.0 / Stopwatch.Frequency;
            return ticks * 1.0 / Stopwatch.Frequency * Math.Pow(10, 3);
        }

    }

    public struct Param
    {
        public int id;
        public int port_num;
        public ulong initial_seq_no;
        public int []num_req_cnt_a;
        public double []latency_cnt_ms_a;
        public int[] instant_req_cnt_a;
    }

    public abstract class ClientBase
    {
        protected System.Net.Sockets.UdpClient udpClient;
        public static List<IPEndPoint> endpoints;
        public static IPAddress my_addr;

        public static uint encodedClientAddress()
        {
            byte[] asbytes = my_addr.GetAddressBytes();
            return ExtractBE32(asbytes, 0);
        }

        public static void StartThread(object p)
        {
            Thread.Sleep(3000);
            var param = (Param)p;
            // var c = new Client();
            var c = new CMClient();
            c.Main(param.id, param.port_num, param.initial_seq_no, param.num_req_cnt_a, param.latency_cnt_ms_a, param.instant_req_cnt_a);
        }

        static public IEnumerable<Thread> StartThreads<T>(int num_threads, int port_num, ulong initial_seq_no, int[] num_req_cnt_a_, double[] latency_cnt_ms_a_, int[] instant_req_cnt_a_) where T : ClientBase, new()
        {
            if (num_threads < 1)
            {
                throw new ArgumentException("number of threads must be at least 1", "num_threads");
            }

            for (int i = 0; i < num_threads; ++i)
            {
                var t = new Thread(StartThread);
                var p = new Param
                {
                    id = i,
                    port_num = port_num,
                    initial_seq_no = initial_seq_no,
                    num_req_cnt_a = num_req_cnt_a_,
                    latency_cnt_ms_a = latency_cnt_ms_a_,
                    instant_req_cnt_a = instant_req_cnt_a_
                };
                t.Start(p);
                yield return t;
            }
        }

        public ClientBase() { }

        protected abstract void Main(int id, int port_num, ulong initial_seq_no, int[] num_req_cnt_a_, double[] latency_cnt_ms_a_, int[] instant_req_cnt_a_);

        protected void Send(MessageBase msg, IPEndPoint remote)
        {
            var a = msg.ToBigEndianByteArray();
            if (this.udpClient.Send(a, a.Length, remote) != a.Length)
            {
                throw new InvalidOperationException("failed to send complete message.");
            }
        }

        protected byte[] Receive()
        {
            IPEndPoint endpoint = null;
            return this.udpClient.Receive(ref endpoint);
        }

        public ulong MyAddress64()
        {
            IPEndPoint ep = (IPEndPoint)udpClient.Client.LocalEndPoint;
            ushort port = (ushort)ep.Port;
            uint addr = encodedClientAddress();
            MemoryStream str = new MemoryStream();
            ushort preamble = 0;
            var bytes = BitConverter.GetBytes(preamble);
            str.Write(bytes, 0, bytes.Length);
            bytes = BitConverter.GetBytes(addr);
            if (BitConverter.IsLittleEndian)
            {
                Array.Reverse(bytes);
            }
            str.Write(bytes, 0, bytes.Length);
            bytes = BitConverter.GetBytes(port);
            if (BitConverter.IsLittleEndian)
            {
                Array.Reverse(bytes);
            }
            str.Write(bytes, 0, bytes.Length);
            byte[] s = str.ToArray();
            Array.Reverse(s);
            return BitConverter.ToUInt64(s, 0);
        }

        public static UInt64 ExtractBE64(byte[] byteArray, int offset)
        {
            byte[] extractedBytes = byteArray.Skip(offset).Take(8).ToArray();
            Array.Reverse(extractedBytes);
            return BitConverter.ToUInt64(extractedBytes, 0);
        }

        public static UInt32 ExtractBE32(byte[] byteArray, int offset)
        {
            byte[] extractedBytes = byteArray.Skip(offset).Take(4).ToArray();
            Array.Reverse(extractedBytes);
            return BitConverter.ToUInt32(extractedBytes, 0);
        }
    }


    public abstract class MessageBase
    {
        public ulong CaseId { get; private set; }

        protected MessageBase(ulong caseId)
        {
            this.CaseId = caseId;
        }

        public abstract byte[] ToBigEndianByteArray();

        public byte[] ToByteArray()
        {
            return this.ToBigEndianByteArray();
        }

        public static void EncodeUlong(MemoryStream memStream, ulong value)
        {
            if (null == memStream)
            {
                throw new ArgumentNullException("memStream");
            }

            var bytes = BitConverter.GetBytes(value);
            if (BitConverter.IsLittleEndian)
            {
                Array.Reverse(bytes);
            }
            memStream.Write(bytes, 0, bytes.Length);
        }

        protected void EncodeBool(MemoryStream memStream, bool value)
        {
            MessageBase.EncodeUlong(memStream, value ? 1UL : 0);
        }

        protected void EncodeBytes(MemoryStream memStream, byte[] value)
        {
            if (null == value)
            {
                throw new ArgumentNullException("value");
            }

            MessageBase.EncodeUlong(memStream, (ulong)value.Length);
            memStream.Write(value, 0, value.Length);
        }

        protected void EncodeHeader(MemoryStream memStream)
        {
            MessageBase.EncodeUlong(memStream, CaseId);
        }

        public static ulong DecodeUlong(byte[] data, ref int offset)
        {
            byte[] bytes = new byte[8];
            Buffer.BlockCopy(data, offset, bytes, 0, 8);
            if (BitConverter.IsLittleEndian)
                Array.Reverse(bytes);
            offset += 8;
            return BitConverter.ToUInt64(bytes, 0);
        }

        protected static byte[] DecodeBytes(byte[] data, ref int offset)
        {
            ulong len = DecodeUlong(data, ref offset);
            byte[] value = new byte[len];
            Buffer.BlockCopy(data, offset, value, 0, (int)len);
            offset += (int)len;
            return value;
        }
    }

    public static class MessageHelper
    {
        public static ulong DecodeUlong(byte[] data, ref int offset)
        {
            byte[] bytes = new byte[8];
            Buffer.BlockCopy(data, offset, bytes, 0, 8);
            if (BitConverter.IsLittleEndian)
                Array.Reverse(bytes);
            offset += 8;
            return BitConverter.ToUInt64(bytes, 0);
        }

        public static byte[] DecodeBytes(byte[] data, ref int offset)
        {
            ulong len = DecodeUlong(data, ref offset);
            byte[] value = new byte[len];
            Buffer.BlockCopy(data, offset, value, 0, (int)len);
            offset += (int)len;
            return value;
        }
    }

}
