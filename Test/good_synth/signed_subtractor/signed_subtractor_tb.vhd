library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity signed_subtractor_tb is
  generic (N : integer := 5);
end entity;

architecture behavioural of signed_subtractor_tb is
  component signed_subtractor is
    port(
      xs : in std_logic_vector (N-1 downto 0);
      ys : in std_logic_vector (N-1 downto 0);
      res : out std_logic_vector (N downto 0)
      );
  end component;

  signal a,b : signed (N-1 downto 0);
  signal c : signed (N downto 0);
  constant A_MIN : integer := -(2**(a'length-1));
  constant B_MIN : integer := -(2**(b'length-1));
  constant A_MAX : integer := 2**(a'length-1)-1;
  constant B_MAX : integer := 2**(b'length-1)-1;

begin

  uut : signed_subtractor port map(
    xs =>std_logic_vector(a),
    ys =>std_logic_vector(b),
    signed(res) => c);

  process is
  begin
    for i in A_MIN to A_MAX loop
      for j in B_MIN to B_MAX loop
        a <= to_signed(i,a'length);
        b <= to_signed(j,b'length);
        wait for 2 ns;
        assert (std_logic_vector(c) = std_logic_vector(to_signed(i-j,c'length)))
          report "error" severity failure;
      end loop;
    end loop;
    wait;
  end process;

end behavioural;
