library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity full_adder_tb is
  generic (N : integer := 1);
end entity;

architecture behavioural of full_adder_tb is
  component full_adder is
    port(
      xs : in std_logic_vector (N-1 downto 0);
      ys : in std_logic_vector (N-1 downto 0);
      cin : in std_logic_vector (N-1 downto 0);
      res : out std_logic_vector (N downto 0)
      );
  end component;

  signal a,b,cin : unsigned (N-1 downto 0);
  signal c : unsigned (N downto 0);
  constant A_MAX : integer := 2**(a'length)-1;
  constant B_MAX : integer := 2**(b'length)-1;
  constant CIN_MAX : integer := 2**(cin'length)-1;

begin

  uut : full_adder port map(
    xs =>std_logic_vector(a),
    ys =>std_logic_vector(b),
    cin =>std_logic_vector(cin),
    unsigned(res) => c);

  process is
  begin
    for i in 0 to A_MAX loop
      for j in 0 to B_MAX loop
        for k in 0 to CIN_MAX loop
          a <= to_unsigned(i,a'length);
          b <= to_unsigned(j,b'length);
          cin <= to_unsigned(k,cin'length);
          wait for 2 ns;
          assert (std_logic_vector(c) = std_logic_vector(to_unsigned(i+j+k,c'length)))
            report "error" severity failure;
        end loop;
      end loop;
    end loop;
    wait;
  end process;

end behavioural;
