namespace IronRSLClient
{
    using System;
    using System.IO;
    using System.Net;
    using System.Threading;
    using System.Diagnostics;
    using System.Linq;
    using System.Collections.Generic;


    public class ReadMessage : MessageBase
    {
        public ulong Opn { get; }
        public ulong Key { get; }
        public Dependency Deps { get; }

        public ReadMessage(ulong opn, ulong key, Dependency deps)
            : base(0) { Opn = opn; Key = key; Deps = deps; }

        public override byte[] ToBigEndianByteArray()
        {
            using (MemoryStream ms = new MemoryStream())
            {
                EncodeHeader(ms);                     // caseId = 0
                // ❌ 删除这行：MessageBase.EncodeUlong(ms, 3);
                // ✅ Tuple直接序列化内容，无长度前缀
                
                MessageBase.EncodeUlong(ms, Opn);
                MessageBase.EncodeUlong(ms, Key);
                
                byte[] depsBytes = Deps.Marshall();
                ms.Write(depsBytes, 0, depsBytes.Length);
                
                return ms.ToArray();
            }
        }

        public static ReadMessage Parse(byte[] data, ref int offset)
        {
            // ❌ 删除这行：ulong tupleLen = MessageBase.DecodeUlong(data, ref offset);
            // ❌ 删除检查：if (tupleLen != 3) throw...
            // ✅ 直接解析tuple内容

            ulong opn = MessageBase.DecodeUlong(data, ref offset);
            ulong key = MessageBase.DecodeUlong(data, ref offset);
            Dependency deps = Dependency.Parse(data, ref offset);
            return new ReadMessage(opn, key, deps);
        }
    }

    public class ReadReplyMessage : MessageBase
    {
        public ulong Opn { get; }
        public ulong Key { get; }
        public VectorClock Vc { get; }
        public Dependency Deps { get; }

        public ReadReplyMessage(ulong opn, ulong key, VectorClock vc, Dependency deps)
            : base(1) { Opn = opn; Key = key; Vc = vc; Deps = deps; }

        public override byte[] ToBigEndianByteArray()
        {
            using (MemoryStream ms = new MemoryStream())
            {
                EncodeHeader(ms);                       // caseId = 1
                // ❌ 删除这行：MessageBase.EncodeUlong(ms, 4);
                // ✅ Tuple直接序列化内容，无长度前缀
                
                MessageBase.EncodeUlong(ms, Opn);
                MessageBase.EncodeUlong(ms, Key);
                
                byte[] vcBytes = Vc.Marshall();
                ms.Write(vcBytes, 0, vcBytes.Length);
                
                byte[] depsBytes = Deps.Marshall();
                ms.Write(depsBytes, 0, depsBytes.Length);
                
                return ms.ToArray();
            }
        }

        public static ReadReplyMessage Parse(byte[] data, ref int offset)
        {
            // ❌ 删除这行：ulong tupleLen = MessageBase.DecodeUlong(data, ref offset);
            // ❌ 删除检查：if (tupleLen != 4) throw...
            // ✅ 直接解析tuple内容

            ulong opn = MessageBase.DecodeUlong(data, ref offset);
            ulong key = MessageBase.DecodeUlong(data, ref offset);
            VectorClock vc = VectorClock.Parse(data, ref offset);
            Dependency deps = Dependency.Parse(data, ref offset);
            return new ReadReplyMessage(opn, key, vc, deps);
        }
    }

    public class WriteMessage : MessageBase
    {
        public ulong Opn { get; }
        public ulong Key { get; }
        public Dependency Deps { get; }
        public Local LocalData { get; }
        public VectorClock Vc { get; }  // 新增 VectorClock 字段

        public WriteMessage(ulong opn, ulong key, Dependency deps, Local local, VectorClock vc)
            : base(2) 
        { 
            Opn = opn; 
            Key = key; 
            Deps = deps; 
            LocalData = local; 
            Vc = vc;  // 初始化 VectorClock
        }

        public override byte[] ToBigEndianByteArray()
        {
            using (MemoryStream ms = new MemoryStream())
            {
                EncodeHeader(ms);       // caseId = 2
                // ❌ 删除这行：MessageBase.EncodeUlong(ms, 4);
                // ✅ Tuple直接序列化内容，无长度前缀
                
                MessageBase.EncodeUlong(ms, Opn);
                MessageBase.EncodeUlong(ms, Key);
                
                byte[] depsBytes = Deps.Marshall();
                ms.Write(depsBytes, 0, depsBytes.Length);
                
                byte[] localBytes = LocalData.Marshall();
                ms.Write(localBytes, 0, localBytes.Length);
                
                // 新增：序列化 VectorClock
                byte[] vcBytes = Vc.Marshall();
                ms.Write(vcBytes, 0, vcBytes.Length);
                
                return ms.ToArray();
            }
        }

        public static WriteMessage Parse(byte[] data, ref int offset)
        {
            // ❌ 删除这行：ulong tupleLen = MessageBase.DecodeUlong(data, ref offset);
            // ❌ 删除检查：if (tupleLen != 4) throw...
            // ✅ 直接解析tuple内容

            ulong opn = MessageBase.DecodeUlong(data, ref offset);
            ulong key = MessageBase.DecodeUlong(data, ref offset);
            Dependency deps = Dependency.Parse(data, ref offset);
            Local local = Local.Parse(data, ref offset);
            VectorClock vc = VectorClock.Parse(data, ref offset);  // 新增：解析 VectorClock
            
            return new WriteMessage(opn, key, deps, local, vc);
        }
    }

    public class WriteReplyMessage : MessageBase
    {
        public ulong Opn { get; }
        public ulong Key { get; }
        public VectorClock Vc { get; }

        public WriteReplyMessage(ulong opn, ulong key, VectorClock vc)
            : base(3) { Opn = opn; Key = key; Vc = vc; }

        public override byte[] ToBigEndianByteArray()
        {
            using (MemoryStream ms = new MemoryStream())
            {
                EncodeHeader(ms);                       // caseId = 3
                // ❌ 删除这行：MessageBase.EncodeUlong(ms, 3);
                // ✅ Tuple直接序列化内容，无长度前缀
                
                MessageBase.EncodeUlong(ms, Opn);
                MessageBase.EncodeUlong(ms, Key);
                
                byte[] vcBytes = Vc.Marshall();
                ms.Write(vcBytes, 0, vcBytes.Length);
                
                return ms.ToArray();
            }
        }

        public static WriteReplyMessage Parse(byte[] data, ref int offset)
        {
            // ❌ 删除这行：ulong tupleLen = MessageBase.DecodeUlong(data, ref offset);
            // ❌ 删除检查：if (tupleLen != 3) throw...
            // ✅ 直接解析tuple内容

            ulong opn = MessageBase.DecodeUlong(data, ref offset);
            ulong key = MessageBase.DecodeUlong(data, ref offset);
            VectorClock vc = VectorClock.Parse(data, ref offset);
            return new WriteReplyMessage(opn, key, vc);
        }
    }

    // public class CMClient : ClientBase
    // {
    //     private int Id;
    //     private ulong Opn;
    //     private Local LocalStore;
    //     private Dependency Deps;
    //     private Random rng = new Random();

    //     // Benchmark 统计数组
    //     private int[] num_req_cnt_a;
    //     private double[] latency_cnt_ms_a;
    //     private int[] instant_req_cnt_a;

    //     // 记录未完成请求的开始时间
    //     private Dictionary<ulong, long> pendingRequests = new Dictionary<ulong, long>();

    //     // 最大 Key 空间 (根据 Dafny MaxKeys)
    //     private const int MaxKeys = 20;

    //     // 清理阈值
    //     private const int CleanupThreshold = 4;

    //     // 工作负载参数
    //     private double readRatio = 0;        // 读请求比例 (默认90%读，10%写)
    //     private double skewRatio = 0.9;        // skew比例 (默认80%的请求)
    //     private double hotKeyRatio = 0.1;      // 热点key比例 (默认访问前20%的key)

    //     protected override void Main(int id, int port_num, ulong initial_seq_no,
    //                                 int[] num_req_cnt_a, double[] latency_cnt_ms_a,
    //                                 int[] instant_req_cnt_a)
    //     {
    //         // 保存统计数组引用
    //         this.num_req_cnt_a = num_req_cnt_a;
    //         this.latency_cnt_ms_a = latency_cnt_ms_a;
    //         this.instant_req_cnt_a = instant_req_cnt_a;

    //         // 从环境变量或配置读取工作负载参数
    //         ReadWorkloadConfig();

    //         // 初始化网络和客户端状态
    //         this.udpClient = new System.Net.Sockets.UdpClient(port_num+(int)id);
    //         this.Id = id;
    //         this.Opn = 0;
    //         this.LocalStore = new Local();
    //         this.Deps = new Dependency();

    //         int actualPort = port_num + id;
    //         Console.WriteLine($"[Client {Id}] Started at port {actualPort}");
    //         Console.WriteLine($"[Client {Id}] Workload: {readRatio:P1} read, skew={skewRatio:P1} req -> {hotKeyRatio:P1} keys");

    //         while (true)
    //         {
    //             // 检查是否需要清理
    //             CheckAndCleanup();

    //             // 根据读写比例决定操作类型
    //             if (rng.NextDouble() < readRatio) {
    //                 SendRead();
    //             }
    //             else
    //             {
    //                 SendWrite();
    //             }

    //             // 接收消息
    //             byte[] data = Receive();
    //             int offset = 0;
    //             ulong caseId = MessageBase.DecodeUlong(data, ref offset);

    //             MessageBase msg = null;
    //             switch (caseId)
    //             {
    //                 case 0: msg = ReadMessage.Parse(data, ref offset); break;
    //                 case 1: msg = ReadReplyMessage.Parse(data, ref offset); break;
    //                 case 2: msg = WriteMessage.Parse(data, ref offset); break;
    //                 case 3: msg = WriteReplyMessage.Parse(data, ref offset); break;
    //                 default:
    //                     Console.WriteLine($"[Client {Id}] Unknown message type: {caseId}");
    //                     continue;
    //             }

    //             switch (msg)
    //             {
    //                 case ReadReplyMessage rr: HandleReadReply(rr); break;
    //                 case WriteReplyMessage wr: HandleWriteReply(wr); break;
    //             }
    //         }
    //     }

    //     private void ReadWorkloadConfig()
    //     {
    //         // 从环境变量读取配置，如果没有则使用默认值
    //         string readRatioStr = Environment.GetEnvironmentVariable("READ_RATIO");
    //         if (!string.IsNullOrEmpty(readRatioStr) && double.TryParse(readRatioStr, out double parsedReadRatio))
    //         {
    //             readRatio = Math.Max(0.0, Math.Min(1.0, parsedReadRatio));
    //         }

    //         string skewRatioStr = Environment.GetEnvironmentVariable("SKEW_RATIO");
    //         if (!string.IsNullOrEmpty(skewRatioStr) && double.TryParse(skewRatioStr, out double parsedSkewRatio))
    //         {
    //             skewRatio = Math.Max(0.0, Math.Min(1.0, parsedSkewRatio));
    //         }

    //         string hotKeyRatioStr = Environment.GetEnvironmentVariable("HOT_KEY_RATIO");
    //         if (!string.IsNullOrEmpty(hotKeyRatioStr) && double.TryParse(hotKeyRatioStr, out double parsedHotKeyRatio))
    //         {
    //             hotKeyRatio = Math.Max(0.0, Math.Min(1.0, parsedHotKeyRatio));
    //         }
    //     }

    //     private ulong SelectKey()
    //     {
    //         // 根据skewness选择key
    //         if (rng.NextDouble() < skewRatio)
    //         {
    //             // 访问热点key（前hotKeyRatio比例的key）
    //             int hotKeyCount = Math.Max(1, (int)(MaxKeys * hotKeyRatio));
    //             return (ulong)rng.Next(0, hotKeyCount);
    //         }
    //         else
    //         {
    //             // 访问所有key空间
    //             return (ulong)rng.Next(0, MaxKeys);
    //         }
    //     }

    //     private void CheckAndCleanup()
    //     {
    //         int totalCount = Deps.dep.Count + LocalStore.Data.Count;
            
    //         if (totalCount >= CleanupThreshold)
    //         {
    //             // 清空 Dependencies
    //             int oldDepsCount = Deps.dep.Count;
    //             Deps.dep.Clear();
                
    //             // 清空 LocalStore
    //             int oldLocalCount = LocalStore.Data.Count;
    //             LocalStore.Data.Clear();
    //         }
    //     }

    //     private void SendRead()
    //     {
    //         ulong key = SelectKey();  // 使用skewness选择key

    //         this.Opn++;
    //         ReadMessage msg = new ReadMessage(Opn, key, Deps);
    //         IPEndPoint server = endpoints[rng.Next(endpoints.Count)];
    //         Send(msg, server);

    //         // 更新请求计数
    //         instant_req_cnt_a[Id]++;
    //         num_req_cnt_a[Id]++;

    //         // 记录开始时间
    //         pendingRequests[Opn] = HiResTimer.Ticks;
    //     }

    //     private void HandleReadReply(ReadReplyMessage msg)
    //     {
    //         // 更新 deps
    //         Dependency delta = new Dependency(new System.Collections.Generic.Dictionary<ulong, VectorClock>
    //         {
    //             { msg.Key, msg.Vc }
    //         });
    //         this.Deps.Merge(delta);

    //         // 统计延迟
    //         if (pendingRequests.TryGetValue(msg.Opn, out long startTicks))
    //         {
    //             double latency = HiResTimer.TicksToMilliseconds(HiResTimer.Ticks - startTicks);
    //             latency_cnt_ms_a[Id] += latency;
    //             pendingRequests.Remove(msg.Opn);
    //         }
    //     }

    //     private void SendWrite()
    //     {
    //         ulong key = SelectKey();  // 使用skewness选择key

    //         this.Opn++;
    //         WriteMessage msg = new WriteMessage(Opn, key, Deps, LocalStore);
    //         IPEndPoint server = endpoints[rng.Next(endpoints.Count)];
    //         Send(msg, server);

    //         // 更新请求计数
    //         instant_req_cnt_a[Id]++;
    //         num_req_cnt_a[Id]++;

    //         // 记录开始时间
    //         pendingRequests[Opn] = HiResTimer.Ticks;
    //     }

    //     private void HandleWriteReply(WriteReplyMessage msg)
    //     {
    //         // 更新本地 cache
    //         Meta meta = new Meta(msg.Key, msg.Vc, this.Deps);
    //         this.LocalStore.Data[msg.Key] = meta;

    //         // 统计延迟
    //         if (pendingRequests.TryGetValue(msg.Opn, out long startTicks))
    //         {
    //             double latency = HiResTimer.TicksToMilliseconds(HiResTimer.Ticks - startTicks);
    //             latency_cnt_ms_a[Id] += latency;
    //             pendingRequests.Remove(msg.Opn);
    //         }
    //     }

    //     // 静态Trace方法（如果需要的话）
    //     public static void Trace(string message)
    //     {
    //         Console.WriteLine($"[TRACE] {message}");
    //     }

    //     // 用于测试的方法：显示key分布统计
    //     private Dictionary<ulong, int> keyAccessCount = new Dictionary<ulong, int>();
        
    //     private void TrackKeyAccess(ulong key)
    //     {
    //         if (!keyAccessCount.ContainsKey(key))
    //             keyAccessCount[key] = 0;
    //         keyAccessCount[key]++;
    //     }

    //     public void PrintKeyDistribution()
    //     {
    //         if (keyAccessCount.Count == 0) return;
            
    //         Console.WriteLine($"[Client {Id}] Key access distribution:");
    //         var sortedKeys = keyAccessCount.OrderByDescending(kv => kv.Value).Take(10);
    //         foreach (var kv in sortedKeys)
    //         {
    //             Console.WriteLine($"  Key {kv.Key}: {kv.Value} accesses");
    //         }
    //     }
    // }

    public class CMClient : ClientBase
    {
        private int Id;
        private ulong Opn;
        private Local LocalStore;
        private Dependency Deps;
        private Random rng = new Random();

        // 新增：维护最大向量时钟
        private VectorClock max_vc;
        
        // 新增：维护总依赖关系
        private Dependency total_deps;

        // Benchmark 统计数组
        private int[] num_req_cnt_a;
        private double[] latency_cnt_ms_a;
        private int[] instant_req_cnt_a;

        // 分别统计读写操作
        private int readCount = 0;
        private int writeCount = 0;
        private double totalReadLatency = 0.0;
        private double totalWriteLatency = 0.0;

        // 记录未完成请求的开始时间和类型
        private Dictionary<ulong, (long startTicks, bool isRead)> pendingRequests = new Dictionary<ulong, (long, bool)>();

        // 最大 Key 空间 (根据 Dafny MaxKeys)
        private const int MaxKeys = 20;

        // 清理阈值
        private const int CleanupThreshold = 50;

        // 工作负载参数
        private double readRatio = 0.5;        // 读请求比例 (默认90%读，10%写)
        private double skewRatio = 0.9;        // skew比例 (默认80%的请求)
        private double hotKeyRatio = 0.1;      // 热点key比例 (默认访问前20%的key)

        // 统计报告相关
        private DateTime lastStatsReport = DateTime.Now;
        private readonly TimeSpan statsInterval = TimeSpan.FromSeconds(10);

        protected override void Main(int id, int port_num, ulong initial_seq_no,
                                    int[] num_req_cnt_a, double[] latency_cnt_ms_a,
                                    int[] instant_req_cnt_a)
        {
            // 保存统计数组引用
            this.num_req_cnt_a = num_req_cnt_a;
            this.latency_cnt_ms_a = latency_cnt_ms_a;
            this.instant_req_cnt_a = instant_req_cnt_a;

            // 初始化 max_vc 为全0向量时钟
            int numServers = endpoints?.Count ?? 3; // 使用服务器数量，如果未知则默认3
            this.max_vc = new VectorClock(new ulong[numServers]); // 创建全0向量时钟 

            // 初始化 total_deps
            this.total_deps = new Dependency();

            // 从环境变量或配置读取工作负载参数
            ReadWorkloadConfig();

            // 初始化网络和客户端状态
            this.udpClient = new System.Net.Sockets.UdpClient(port_num+(int)id);
            this.Id = id;
            this.Opn = 0;
            this.LocalStore = new Local();
            this.Deps = new Dependency();

            int actualPort = port_num + id;
            Console.WriteLine($"[Client {Id}] Started at port {actualPort}");
            Console.WriteLine($"[Client {Id}] Workload: {readRatio:P1} read, skew={skewRatio:P1} req -> {hotKeyRatio:P1} keys");

            while (true)
            {
                // 检查是否需要清理
                CheckAndCleanup();

                // 定期报告统计信息
                ReportStatsIfNeeded();

                // 根据读写比例决定操作类型
                if (rng.NextDouble() < readRatio) {
                    SendRead();
                }
                else
                {
                    SendWrite();
                }

                // 接收消息
                byte[] data = Receive();
                int offset = 0;
                ulong caseId = MessageBase.DecodeUlong(data, ref offset);

                MessageBase msg = null;
                switch (caseId)
                {
                    case 0: msg = ReadMessage.Parse(data, ref offset); break;
                    case 1: msg = ReadReplyMessage.Parse(data, ref offset); break;
                    case 2: msg = WriteMessage.Parse(data, ref offset); break;
                    case 3: msg = WriteReplyMessage.Parse(data, ref offset); break;
                    default:
                        Console.WriteLine($"[Client {Id}] Unknown message type: {caseId}");
                        continue;
                }

                switch (msg)
                {
                    case ReadReplyMessage rr: HandleReadReply(rr); break;
                    case WriteReplyMessage wr: HandleWriteReply(wr); break;
                }
            }
        }

        private void ReadWorkloadConfig()
        {
            // 从环境变量读取配置，如果没有则使用默认值
            string readRatioStr = Environment.GetEnvironmentVariable("READ_RATIO");
            if (!string.IsNullOrEmpty(readRatioStr) && double.TryParse(readRatioStr, out double parsedReadRatio))
            {
                readRatio = Math.Max(0.0, Math.Min(1.0, parsedReadRatio));
            }

            string skewRatioStr = Environment.GetEnvironmentVariable("SKEW_RATIO");
            if (!string.IsNullOrEmpty(skewRatioStr) && double.TryParse(skewRatioStr, out double parsedSkewRatio))
            {
                skewRatio = Math.Max(0.0, Math.Min(1.0, parsedSkewRatio));
            }

            string hotKeyRatioStr = Environment.GetEnvironmentVariable("HOT_KEY_RATIO");
            if (!string.IsNullOrEmpty(hotKeyRatioStr) && double.TryParse(hotKeyRatioStr, out double parsedHotKeyRatio))
            {
                hotKeyRatio = Math.Max(0.0, Math.Min(1.0, parsedHotKeyRatio));
            }
        }

        private ulong SelectKey()
        {
            // 根据skewness选择key
            if (rng.NextDouble() < skewRatio)
            {
                // 访问热点key（前hotKeyRatio比例的key）
                int hotKeyCount = Math.Max(1, (int)(MaxKeys * hotKeyRatio));
                return (ulong)rng.Next(0, hotKeyCount);
            }
            else
            {
                // 访问所有key空间
                return (ulong)rng.Next(0, MaxKeys);
            }
        }

        private void CheckAndCleanup()
        {
            int totalCount = Deps.dep.Count + LocalStore.Data.Count;
            
            if (totalCount >= CleanupThreshold)
            {
                // 清空 Dependencies
                int oldDepsCount = Deps.dep.Count;
                Deps.dep.Clear();
                
                // 清空 LocalStore
                int oldLocalCount = LocalStore.Data.Count;
                LocalStore.Data.Clear();
                
                // 清空 total_deps
                int oldTotalDepsCount = total_deps.dep.Count;
                total_deps.dep.Clear();
                
                // Console.WriteLine($"[Client {Id}] Cleanup: Cleared {oldDepsCount} deps, {oldLocalCount} local entries, {oldTotalDepsCount} total_deps");
            }
        }

        private void ReportStatsIfNeeded()
        {
            DateTime now = DateTime.Now;
            if (now - lastStatsReport >= statsInterval)
            {
                ReportDetailedStats();
                lastStatsReport = now;
            }
        }

        private void ReportDetailedStats()
        {
            int totalRequests = readCount + writeCount;
            if (totalRequests == 0) return;

            double avgReadLatency = readCount > 0 ? totalReadLatency / readCount : 0;
            double avgWriteLatency = writeCount > 0 ? totalWriteLatency / writeCount : 0;
            double avgOverallLatency = (totalReadLatency + totalWriteLatency) / totalRequests;

            Console.WriteLine($"[Client {Id}] Stats Report:");
            Console.WriteLine($"  Total Requests: {totalRequests} (Read: {readCount}, Write: {writeCount})");
            Console.WriteLine($"  Avg Read Latency: {avgReadLatency:F2} ms");
            Console.WriteLine($"  Avg Write Latency: {avgWriteLatency:F2} ms");
            Console.WriteLine($"  Avg Overall Latency: {avgOverallLatency:F2} ms");
            // Console.WriteLine($"  Pending Requests: {pendingRequests.Count}");
            // Console.WriteLine($"  Max VC: {max_vc}"); // 添加max_vc的显示
            // Console.WriteLine($"  Total Deps Size: {total_deps.dep.Count}"); // 添加total_deps大小的显示
        }

        private void SendRead()
        {
            ulong key = SelectKey();  // 使用skewness选择key

            this.Opn++;
            ReadMessage msg = new ReadMessage(Opn, key, Deps);
            IPEndPoint server = endpoints[rng.Next(endpoints.Count)];
            Send(msg, server);

            // 更新请求计数
            instant_req_cnt_a[Id]++;
            num_req_cnt_a[Id]++;

            // 记录开始时间和请求类型
            pendingRequests[Opn] = (HiResTimer.Ticks, true);  // true表示读请求
        }

        private void HandleReadReply(ReadReplyMessage msg)
        {
            // 合并 vc_rreply 到 max_vc
            if (msg.Vc != null)
            {
                // max_vc = VectorClock.Merge(max_vc, msg.Vc);
                max_vc.Merge(msg.Vc);
            }

            // 更新 deps 和 total_deps
            Dependency delta = new Dependency(new System.Collections.Generic.Dictionary<ulong, VectorClock>
            {
                { msg.Key, msg.Vc }
            });
            this.Deps.Merge(delta);
            
            // 同时合并到 total_deps
            this.total_deps.Merge(delta);

            // 统计延迟
            if (pendingRequests.TryGetValue(msg.Opn, out var requestInfo))
            {
                double latency = HiResTimer.TicksToMilliseconds(HiResTimer.Ticks - requestInfo.startTicks);
                
                // 更新总体统计
                latency_cnt_ms_a[Id] += latency;
                
                // 更新读请求专门统计
                if (requestInfo.isRead)
                {
                    readCount++;
                    totalReadLatency += latency;
                }
                else
                {
                    // 这不应该发生，但为了安全处理
                    Console.WriteLine($"[Client {Id}] Warning: Read reply for non-read request {msg.Opn}");
                }
                
                pendingRequests.Remove(msg.Opn);
            }
            else
            {
                Console.WriteLine($"[Client {Id}] Warning: Received read reply for unknown request {msg.Opn}");
            }
        }

        private void SendWrite()
        {
            ulong key = SelectKey();  // 使用skewness选择key

            this.Opn++;
            WriteMessage msg = new WriteMessage(Opn, key, total_deps, LocalStore, max_vc);
            IPEndPoint server = endpoints[rng.Next(endpoints.Count)];
            Send(msg, server);

            // 更新请求计数
            instant_req_cnt_a[Id]++;
            num_req_cnt_a[Id]++;

            // 记录开始时间和请求类型
            pendingRequests[Opn] = (HiResTimer.Ticks, false);  // false表示写请求
        }

        private void HandleWriteReply(WriteReplyMessage msg)
        {
            // 合并 vc_wreply 到 max_vc
            if (msg.Vc != null)
            {
                // max_vc = VectorClock.Merge(max_vc, msg.Vc);
                max_vc.Merge(msg.Vc);
            }

            // 更新本地 cache
            Meta meta = new Meta(msg.Key, msg.Vc, this.Deps);
            this.LocalStore.Data[msg.Key] = meta;
            
            // 将 write_reply 中的 key,vc 合并到 total_deps
            if (msg.Vc != null)
            {
                Dependency writeReplyDelta = new Dependency(new System.Collections.Generic.Dictionary<ulong, VectorClock>
                {
                    { msg.Key, msg.Vc }
                });
                this.total_deps.Merge(writeReplyDelta);
            }

            // 统计延迟
            if (pendingRequests.TryGetValue(msg.Opn, out var requestInfo))
            {
                double latency = HiResTimer.TicksToMilliseconds(HiResTimer.Ticks - requestInfo.startTicks);
                
                // 更新总体统计
                latency_cnt_ms_a[Id] += latency;
                
                // 更新写请求专门统计
                if (!requestInfo.isRead)
                {
                    writeCount++;
                    totalWriteLatency += latency;
                }
                else
                {
                    // 这不应该发生，但为了安全处理
                    Console.WriteLine($"[Client {Id}] Warning: Write reply for non-write request {msg.Opn}");
                }
                
                pendingRequests.Remove(msg.Opn);
            }
            else
            {
                Console.WriteLine($"[Client {Id}] Warning: Received write reply for unknown request {msg.Opn}");
            }
        }

        // 在程序结束时调用的最终统计报告
        public void PrintFinalStats()
        {
            Console.WriteLine($"\n[Client {Id}] Final Statistics:");
            Console.WriteLine($"==============================");
            
            int totalRequests = readCount + writeCount;
            if (totalRequests == 0)
            {
                Console.WriteLine($"  No completed requests");
                return;
            }

            double avgReadLatency = readCount > 0 ? totalReadLatency / readCount : 0;
            double avgWriteLatency = writeCount > 0 ? totalWriteLatency / writeCount : 0;
            double avgOverallLatency = (totalReadLatency + totalWriteLatency) / totalRequests;

            Console.WriteLine($"  Total Requests: {totalRequests}");
            Console.WriteLine($"  Read Requests: {readCount} ({(double)readCount / totalRequests:P1})");
            Console.WriteLine($"  Write Requests: {writeCount} ({(double)writeCount / totalRequests:P1})");
            Console.WriteLine($"  Average Read Latency: {avgReadLatency:F3} ms");
            Console.WriteLine($"  Average Write Latency: {avgWriteLatency:F3} ms");
            Console.WriteLine($"  Average Overall Latency: {avgOverallLatency:F3} ms");
            Console.WriteLine($"  Total Read Latency: {totalReadLatency:F3} ms");
            Console.WriteLine($"  Total Write Latency: {totalWriteLatency:F3} ms");
            Console.WriteLine($"  Pending Requests: {pendingRequests.Count}");
            Console.WriteLine($"  Final Max VC: {max_vc}"); // 添加最终max_vc的显示
            Console.WriteLine($"  Final Total Deps Size: {total_deps.dep.Count}"); // 添加最终total_deps大小的显示
        }

        // 获取当前max_vc的方法（供外部访问）
        public VectorClock GetMaxVectorClock()
        {
            return max_vc;
        }

        // 获取当前total_deps的方法（供外部访问）
        public Dependency GetTotalDependencies()
        {
            return total_deps;
        }

        // 静态Trace方法（如果需要的话）
        public static void Trace(string message)
        {
            Console.WriteLine($"[TRACE] {message}");
        }

        // 用于测试的方法：显示key分布统计
        private Dictionary<ulong, int> keyAccessCount = new Dictionary<ulong, int>();
        
        private void TrackKeyAccess(ulong key)
        {
            if (!keyAccessCount.ContainsKey(key))
                keyAccessCount[key] = 0;
            keyAccessCount[key]++;
        }

        public void PrintKeyDistribution()
        {
            if (keyAccessCount.Count == 0) return;
            
            Console.WriteLine($"[Client {Id}] Key access distribution:");
            var sortedKeys = keyAccessCount.OrderByDescending(kv => kv.Value).Take(10);
            foreach (var kv in sortedKeys)
            {
                Console.WriteLine($"  Key {kv.Key}: {kv.Value} accesses");
            }
        }
    }

        public class RequestMessage : MessageBase
        {
            public byte[] Value { get; set; }
            public ulong seqNum;
            public ulong myaddr;

            public RequestMessage(ulong seqNum, ulong myaddr)
                : base(0)
            {
                this.seqNum = seqNum;
                this.myaddr = myaddr;
            }

            public override byte[] ToBigEndianByteArray()
            {
                return this.Encode();
            }

            public ulong GetSeqNum()
            {
                return seqNum;
            }

            private byte[] Encode()
            {

                using (var memStream = new MemoryStream())
                {
                    this.EncodeHeader(memStream); // case for CMessage_Request
                    MessageBase.EncodeUlong(memStream, (ulong)seqNum); // field one in CMessage_Request
                    MessageBase.EncodeUlong(memStream, (ulong)0); // case for CAppMessageIncrement               

                    return memStream.ToArray();
                }
            }
        }

    // public class Client : ClientBase
    // {
    //     public static bool DEBUG = false;

    //     //private static long num_reqs = 0;

    //     // public int []num_req_cnt_a;
    //     // public double []latency_cnt_ms_a;

    //     private int[] instant_req_cnt_a;



    //     public static void Trace(string str)
    //     {
    //         if (DEBUG)
    //         {
    //             Console.Out.WriteLine(str);
    //         }    
    //     }
  

    //     public string ByteArrayToString(byte[] ba)
    //     {
    //         string hex = BitConverter.ToString(ba);
    //         return hex.Replace("-", "");
    //     }

    //     protected void ReceiveLoop() {
    //         byte[] bytes;
    //         while (true)
    //         {
    //             bytes = Receive();
    //             var end_time = (ulong)HiResTimer.Ticks;
    //             Trace("Got the following reply:" + ByteArrayToString(bytes));
    //             if (bytes.Length == 40)
    //             {
    //                 var start_time = ExtractBE64(bytes, 32);
    //                 var request_time = end_time - start_time;

    //                 Trace("Request took " + request_time + " ticks");
    //                 Console.WriteLine(request_time);
    //             }
    //             else
    //             {
    //                 Trace("Got an unexpected packet length: " + bytes.Length);
    //             }
    //         }
    //     }

    //     protected override void Main(int id, int port_num, ulong initial_seq_no, int []num_req_cnt_a_, double []latency_cnt_ms_a_, int[] instant_req_cnt_a_)
    //     {
    //         this.instant_req_cnt_a = instant_req_cnt_a_;
    //         this.udpClient = new System.Net.Sockets.UdpClient(port_num+(int)id);
    //         this.udpClient.Client.ReceiveTimeout = 20;
    //         // this.num_req_cnt_a = num_req_cnt_a_;
    //         // this.latency_cnt_ms_a = latency_cnt_ms_a_;
    //         ulong myaddr = MyAddress64();
            

    //         int serverIdx = 0;
            
    //         for (ulong seq_no = initial_seq_no; true; ++seq_no)
    //         {
    //             // Make the sequence number a time stamp
    //             //var newSeqNum = (ulong) HiResTimer.UtcNow.Ticks;
    //             //if (newSeqNum == seqNum) {
    //             //    seqNum = newSeqNum + 1;
    //             //}
    //             //else
    //             //{
    //             //    seqNum = newSeqNum;
    //             //}

    //             var msg = new RequestMessage(seq_no, myaddr);

    //             Trace("Client " + id.ToString() + ": Sending a request with a sequence number " + msg.GetSeqNum() + " to " + ClientBase.endpoints[serverIdx].ToString());

    //             var start_time = HiResTimer.Ticks;
    //             this.Send(msg, ClientBase.endpoints[serverIdx]);
    //             //foreach (var remote in ClientBase.endpoints)
    //             //{
    //             //    this.Send(msg, remote);
    //             //}

    //             // Wait for the reply
    //             var received_reply = false;
    //             while (!received_reply)
    //             {
    //                 byte[] bytes;
    //                 try
    //                 {
    //                     bytes = Receive();
    //                 }
    //                 catch (System.Net.Sockets.SocketException e)
    //                 {
    //                     serverIdx = (serverIdx + 1) % ClientBase.endpoints.Count();
    //                     Console.WriteLine("#timeout; rotating to server {0}", serverIdx);
    //                     Console.WriteLine(e.ToString());
    //                     break;
    //                 }
    //                 var end_time = HiResTimer.Ticks;
    //                 Trace("Got the following reply:" + ByteArrayToString(bytes));
    //                 double latency = 0;

    //                 if (bytes.Length == 32)
    //                 {
    //                     var reply_seq_no = ExtractBE64(bytes, offset: 8);
    //                     if (reply_seq_no == seq_no)
    //                     {
    //                         received_reply = true;
    //                         // Report time in milliseconds, since that's what the Python script appears to expect
    //                         latency = HiResTimer.TicksToMilliseconds(end_time - start_time);
    //                         // Console.Out.WriteLine(string.Format("#req{0} {1} {2}", seq_no, latency, id));
    //                         //long n = Interlocked.Increment(ref num_reqs);
    //                         //if (1 == n || n % 1000 == 0)
    //                         //{
    //                         //    Console.WriteLine("{0} requests completed.", n);
    //                         //}
    //                         num_req_cnt_a_[id] += 1;
    //                         latency_cnt_ms_a_[id] += latency;

    //                         instant_req_cnt_a_[id]++;
    //                     } else {
    //                         // Console.Out.WriteLine("reply seq no: {0}", reply_seq_no);
    //                     }
    //                 }
    //                 else
    //                 {
    //                     Console.Error.WriteLine("Got an unexpected packet length: " + bytes.Length);
    //                 }
    //             }
    //         }
    //     }
    // }
}
